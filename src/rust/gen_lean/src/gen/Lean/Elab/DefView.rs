// Lean compiler output
// Module: Lean.Elab.DefView
// Imports: Lean.Elab.DeclNameGen Lean.Elab.DeclUtil
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_getSepArgs, l_Lean_Syntax_isNone, l_Lean_Syntax_mkNumLit, l_Lean_mkIdentFrom,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node4, l_Lean_maxRecDepthErrorMessage,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Attributes::l_Lean_Elab_toAttributeKind___boxed;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_getCurrMacroScope___redArg, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg,
};
use crate::r#gen::Lean::Elab::DeclModifiers::{
    l_Lean_Elab_Modifiers_addAttr, l_Lean_Elab_Modifiers_addFirstAttr,
    l_Lean_Elab_Modifiers_filterAttrs, l_Lean_Elab_instBEqComputeKind_beq,
    l_Lean_Elab_instInhabitedModifiers_default,
};
use crate::r#gen::Lean::Elab::DeclNameGen::{
    initialize_Lean_Elab_DeclNameGen, l_Lean_Elab_Command_mkInstanceName,
    runtime_initialize_Lean_Elab_DeclNameGen,
};
use crate::r#gen::Lean::Elab::DeclUtil::{
    initialize_Lean_Elab_DeclUtil, l_Lean_Elab_expandDeclSig, l_Lean_Elab_expandOptDeclSig,
    runtime_initialize_Lean_Elab_DeclUtil,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go;
use crate::r#gen::Lean::Elab::Util::{
    l_Lean_Elab_expandMacroImpl_x3f, l_Lean_Elab_expandOptNamedPrio___boxed,
    l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::Language::Basic::{
    l_Lean_Language_SnapshotTask_map___redArg, l_Lean_Language_instInhabitedSnapshotTree_default,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_inheritedTraceOptions,
    l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::ffi::{lean_array_size, lean_array_uget_borrowed};
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_string_dec_eq, lean_uint64_of_nat,
    lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static mut l_Lean_Elab_instInhabitedDefKind_default: u8 = 0;
pub static mut l_Lean_Elab_instInhabitedDefKind: u8 = 0;
pub static l_Lean_Elab_instBEqDefKind___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_instBEqDefKind_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instBEqDefKind___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instBEqDefKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instBEqDefKind: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instBEqDefKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0_value:
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
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1_value:
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
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2_value:
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
            l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedDefViewElabHeaderData: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value:
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
    m_fun: l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0_value:
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
static mut l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1_value:
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
    m_fun: l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value:
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
    m_fun: l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [68, 101, 102, 115, 80, 97, 114, 115, 101, 100, 83, 110, 97, 112, 115, 104, 111, 116, 0]};
static mut l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,4408595883411259083 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instImpl_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instTypeNameDefsParsedSnapshot: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__6_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_instInhabitedDefView_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedDefView_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedDefView_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedDefView: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,5908072408641034476 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_DefView_markDefEq___lam__0___closed__0_value:
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
    m_data: [100, 101, 102, 101, 113, 0],
};
static mut l_Lean_Elab_DefView_markDefEq___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_DefView_markDefEq___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4826972851695508558 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_DefView_markDefEq___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_DefView_markDefEq___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_DefView_markDefEq___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_DefView_markDefEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_DefView_markDefEq___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_DefView_markDefEq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_DefView_markDefEq___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [105, 110, 108, 105, 110, 101, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8159932143332935260 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7045040058828669725 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__6_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__3_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__10_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value:
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
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__1_value:
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
    m_data: [100, 101, 99, 108, 73, 100, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value:
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
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__3_value:
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
    m_data: [65, 116, 116, 114, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__3_value)
            as *mut crate::leanh::LeanObject,
        4584992172905639687 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,12927425362287788416 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        109, 107, 73, 110, 115, 116, 97, 110, 99, 101, 78, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,3223284126629939794 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__5_value)
            as *mut crate::leanh::LeanObject,
        15410416404573358003 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__8_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkDefViewOfInstance___closed__10_value:
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
    m_data: [32, 102, 111, 114, 32, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkDefViewOfInstance___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value: crate::leanh::LeanStringObject<
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
        100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13585030837571646948 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 61, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4_value: crate::leanh::LeanStringObject<
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
    m_data: [115, 117, 102, 102, 105, 120, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7625897890118033792 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__4_value)
            as *mut crate::leanh::LeanObject,
        8715860392475343861 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8_value: crate::leanh::LeanStringObject<
    20,
> = crate::leanh::LeanStringObject {
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
        100, 101, 102, 97, 117, 108, 116, 79, 114, 79, 102, 78, 111, 110, 101, 109, 112, 116, 121,
        0,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__7_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__8_value)
            as *mut crate::leanh::LeanObject,
        14701813571789919052 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
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
        100, 101, 102, 97, 117, 108, 116, 95, 111, 114, 95, 111, 102, 78, 111, 110, 101, 109, 112,
        116, 121, 37, 0,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11_value:
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
    m_data: [117, 110, 115, 97, 102, 101, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfExample___closed__0_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfExample___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfExample___closed__1_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [95, 101, 120, 97, 109, 112, 108, 101, 0],
};
static mut l_Lean_Elab_Command_mkDefViewOfExample___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefViewOfExample___closed__2_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8858487489706526963 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfExample___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1_value)
            as *mut crate::leanh::LeanObject,
        1827444229220621555 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_mkDefViewOfExample___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfExample___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_isDefLike___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [116, 104, 101, 111, 114, 101, 109, 0],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_isDefLike___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_isDefLike___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3907549710869165294 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_isDefLike___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [111, 112, 97, 113, 117, 101, 0],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_isDefLike___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_isDefLike___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__3_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__2_value)
                as *mut crate::leanh::LeanObject,
            7407402195942431087 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_isDefLike___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_isDefLike___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11064845058293668901 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Command_isDefLike___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_isDefLike___closed__5_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [101, 120, 97, 109, 112, 108, 101, 0],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_isDefLike___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__6_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_isDefLike___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__6_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__5_value)
                as *mut crate::leanh::LeanObject,
            16587644253004373100 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_isDefLike___closed__7_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [97, 98, 98, 114, 101, 118, 0],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__8_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_isDefLike___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__8_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_isDefLike___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__8_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__7_value)
                as *mut crate::leanh::LeanObject,
            7158170725601883426 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_isDefLike___closed__9_value: crate::leanh::LeanStringObject<11> =
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
static mut l_Lean_Elab_Command_isDefLike___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_isDefLike___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_isDefLike___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__10_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_isDefLike___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__10_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_isDefLike___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__10_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__9_value)
                as *mut crate::leanh::LeanObject,
            9789339221525904376 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_isDefLike___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_mkDefView___closed__0_value: crate::leanh::LeanStringObject<30> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 107, 105, 110, 100, 32, 111, 102,
            32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_Command_mkDefView___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkDefView___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_mkDefView___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkDefView___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_isDefLike___closed__9_value) as *mut crate::leanh::LeanObject,6897119537390546559 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [68, 101, 102, 86, 105, 101, 119, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,530979614227987087 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,16822043437053200418 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,14199109792594499331 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,12046185499159403317 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__0_value) as *mut crate::leanh::LeanObject,7427837794232889372 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3339763488256995113 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7838269638771429444 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,15708863969511340069 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20__value) as *mut crate::leanh::LeanObject,9051532757897805587 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17829560872556345656 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1745620379 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,5347715228956474749 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,507745096295086142 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7792782298071999666 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3010035636668721035 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_DefKind_ctorIdx(mut v_x_2285_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_2285_ {
        0 => {
            let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2286_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2286_;
        }
        1 => {
            let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2287_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2287_;
        }
        2 => {
            let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2288_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2288_;
        }
        3 => {
            let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2289_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2289_;
        }
        4 => {
            let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2290_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_2290_;
        }
        _ => {
            let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2291_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_2291_;
        }
    }
}
pub unsafe fn l_Lean_Elab_DefKind_ctorIdx___boxed(
    mut v_x_2292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2293_: u8 = 0;
    let mut v_res_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2293_ = (crate::leanh::lean_unbox(v_x_2292_) as u8);
    v_res_2294_ = l_Lean_Elab_DefKind_ctorIdx(v_x_boxed_2293_);
    return v_res_2294_;
}
pub unsafe fn l_Lean_Elab_DefKind_toCtorIdx(mut v_x_2295_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2296_ = l_Lean_Elab_DefKind_ctorIdx(v_x_2295_);
    return v___x_2296_;
}
pub unsafe fn l_Lean_Elab_DefKind_toCtorIdx___boxed(
    mut v_x_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_2298_: u8 = 0;
    let mut v_res_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2298_ = (crate::leanh::lean_unbox(v_x_2297_) as u8);
    v_res_2299_ = l_Lean_Elab_DefKind_toCtorIdx(v_x_4__boxed_2298_);
    return v_res_2299_;
}
pub unsafe fn l_Lean_Elab_DefKind_ctorElim___redArg(
    mut v_k_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2300_);
    return v_k_2300_;
}
pub unsafe fn l_Lean_Elab_DefKind_ctorElim___redArg___boxed(
    mut v_k_2301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2302_ = l_Lean_Elab_DefKind_ctorElim___redArg(v_k_2301_);
    crate::leanh::lean_dec(v_k_2301_);
    return v_res_2302_;
}
pub unsafe fn l_Lean_Elab_DefKind_ctorElim(
    mut v_motive_2303_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2304_: *mut crate::leanh::LeanObject,
    mut v_t_2305_: u8,
    mut v_h_2306_: *mut crate::leanh::LeanObject,
    mut v_k_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2307_);
    return v_k_2307_;
}
pub unsafe fn l_Lean_Elab_DefKind_ctorElim___boxed(
    mut v_motive_2308_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2309_: *mut crate::leanh::LeanObject,
    mut v_t_2310_: *mut crate::leanh::LeanObject,
    mut v_h_2311_: *mut crate::leanh::LeanObject,
    mut v_k_2312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2313_: u8 = 0;
    let mut v_res_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2313_ = (crate::leanh::lean_unbox(v_t_2310_) as u8);
    v_res_2314_ = l_Lean_Elab_DefKind_ctorElim(
        v_motive_2308_,
        v_ctorIdx_2309_,
        v_t_boxed_2313_,
        v_h_2311_,
        v_k_2312_,
    );
    crate::leanh::lean_dec(v_k_2312_);
    crate::leanh::lean_dec(v_ctorIdx_2309_);
    return v_res_2314_;
}
pub unsafe fn l_Lean_Elab_DefKind_def_elim___redArg(
    mut v_def_2315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_def_2315_);
    return v_def_2315_;
}
pub unsafe fn l_Lean_Elab_DefKind_def_elim___redArg___boxed(
    mut v_def_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2317_ = l_Lean_Elab_DefKind_def_elim___redArg(v_def_2316_);
    crate::leanh::lean_dec(v_def_2316_);
    return v_res_2317_;
}
pub unsafe fn l_Lean_Elab_DefKind_def_elim(
    mut v_motive_2318_: *mut crate::leanh::LeanObject,
    mut v_t_2319_: u8,
    mut v_h_2320_: *mut crate::leanh::LeanObject,
    mut v_def_2321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_def_2321_);
    return v_def_2321_;
}
pub unsafe fn l_Lean_Elab_DefKind_def_elim___boxed(
    mut v_motive_2322_: *mut crate::leanh::LeanObject,
    mut v_t_2323_: *mut crate::leanh::LeanObject,
    mut v_h_2324_: *mut crate::leanh::LeanObject,
    mut v_def_2325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2326_: u8 = 0;
    let mut v_res_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2326_ = (crate::leanh::lean_unbox(v_t_2323_) as u8);
    v_res_2327_ =
        l_Lean_Elab_DefKind_def_elim(v_motive_2322_, v_t_boxed_2326_, v_h_2324_, v_def_2325_);
    crate::leanh::lean_dec(v_def_2325_);
    return v_res_2327_;
}
pub unsafe fn l_Lean_Elab_DefKind_instance_elim___redArg(
    mut v_instance_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_instance_2328_);
    return v_instance_2328_;
}
pub unsafe fn l_Lean_Elab_DefKind_instance_elim___redArg___boxed(
    mut v_instance_2329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2330_ = l_Lean_Elab_DefKind_instance_elim___redArg(v_instance_2329_);
    crate::leanh::lean_dec(v_instance_2329_);
    return v_res_2330_;
}
pub unsafe fn l_Lean_Elab_DefKind_instance_elim(
    mut v_motive_2331_: *mut crate::leanh::LeanObject,
    mut v_t_2332_: u8,
    mut v_h_2333_: *mut crate::leanh::LeanObject,
    mut v_instance_2334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_instance_2334_);
    return v_instance_2334_;
}
pub unsafe fn l_Lean_Elab_DefKind_instance_elim___boxed(
    mut v_motive_2335_: *mut crate::leanh::LeanObject,
    mut v_t_2336_: *mut crate::leanh::LeanObject,
    mut v_h_2337_: *mut crate::leanh::LeanObject,
    mut v_instance_2338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2339_: u8 = 0;
    let mut v_res_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2339_ = (crate::leanh::lean_unbox(v_t_2336_) as u8);
    v_res_2340_ = l_Lean_Elab_DefKind_instance_elim(
        v_motive_2335_,
        v_t_boxed_2339_,
        v_h_2337_,
        v_instance_2338_,
    );
    crate::leanh::lean_dec(v_instance_2338_);
    return v_res_2340_;
}
pub unsafe fn l_Lean_Elab_DefKind_theorem_elim___redArg(
    mut v_theorem_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_theorem_2341_);
    return v_theorem_2341_;
}
pub unsafe fn l_Lean_Elab_DefKind_theorem_elim___redArg___boxed(
    mut v_theorem_2342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2343_ = l_Lean_Elab_DefKind_theorem_elim___redArg(v_theorem_2342_);
    crate::leanh::lean_dec(v_theorem_2342_);
    return v_res_2343_;
}
pub unsafe fn l_Lean_Elab_DefKind_theorem_elim(
    mut v_motive_2344_: *mut crate::leanh::LeanObject,
    mut v_t_2345_: u8,
    mut v_h_2346_: *mut crate::leanh::LeanObject,
    mut v_theorem_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_theorem_2347_);
    return v_theorem_2347_;
}
pub unsafe fn l_Lean_Elab_DefKind_theorem_elim___boxed(
    mut v_motive_2348_: *mut crate::leanh::LeanObject,
    mut v_t_2349_: *mut crate::leanh::LeanObject,
    mut v_h_2350_: *mut crate::leanh::LeanObject,
    mut v_theorem_2351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2352_: u8 = 0;
    let mut v_res_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2352_ = (crate::leanh::lean_unbox(v_t_2349_) as u8);
    v_res_2353_ = l_Lean_Elab_DefKind_theorem_elim(
        v_motive_2348_,
        v_t_boxed_2352_,
        v_h_2350_,
        v_theorem_2351_,
    );
    crate::leanh::lean_dec(v_theorem_2351_);
    return v_res_2353_;
}
pub unsafe fn l_Lean_Elab_DefKind_example_elim___redArg(
    mut v_example_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_example_2354_);
    return v_example_2354_;
}
pub unsafe fn l_Lean_Elab_DefKind_example_elim___redArg___boxed(
    mut v_example_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2356_ = l_Lean_Elab_DefKind_example_elim___redArg(v_example_2355_);
    crate::leanh::lean_dec(v_example_2355_);
    return v_res_2356_;
}
pub unsafe fn l_Lean_Elab_DefKind_example_elim(
    mut v_motive_2357_: *mut crate::leanh::LeanObject,
    mut v_t_2358_: u8,
    mut v_h_2359_: *mut crate::leanh::LeanObject,
    mut v_example_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_example_2360_);
    return v_example_2360_;
}
pub unsafe fn l_Lean_Elab_DefKind_example_elim___boxed(
    mut v_motive_2361_: *mut crate::leanh::LeanObject,
    mut v_t_2362_: *mut crate::leanh::LeanObject,
    mut v_h_2363_: *mut crate::leanh::LeanObject,
    mut v_example_2364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2365_: u8 = 0;
    let mut v_res_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2365_ = (crate::leanh::lean_unbox(v_t_2362_) as u8);
    v_res_2366_ = l_Lean_Elab_DefKind_example_elim(
        v_motive_2361_,
        v_t_boxed_2365_,
        v_h_2363_,
        v_example_2364_,
    );
    crate::leanh::lean_dec(v_example_2364_);
    return v_res_2366_;
}
pub unsafe fn l_Lean_Elab_DefKind_opaque_elim___redArg(
    mut v_opaque_2367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_opaque_2367_);
    return v_opaque_2367_;
}
pub unsafe fn l_Lean_Elab_DefKind_opaque_elim___redArg___boxed(
    mut v_opaque_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2369_ = l_Lean_Elab_DefKind_opaque_elim___redArg(v_opaque_2368_);
    crate::leanh::lean_dec(v_opaque_2368_);
    return v_res_2369_;
}
pub unsafe fn l_Lean_Elab_DefKind_opaque_elim(
    mut v_motive_2370_: *mut crate::leanh::LeanObject,
    mut v_t_2371_: u8,
    mut v_h_2372_: *mut crate::leanh::LeanObject,
    mut v_opaque_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_opaque_2373_);
    return v_opaque_2373_;
}
pub unsafe fn l_Lean_Elab_DefKind_opaque_elim___boxed(
    mut v_motive_2374_: *mut crate::leanh::LeanObject,
    mut v_t_2375_: *mut crate::leanh::LeanObject,
    mut v_h_2376_: *mut crate::leanh::LeanObject,
    mut v_opaque_2377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2378_: u8 = 0;
    let mut v_res_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2378_ = (crate::leanh::lean_unbox(v_t_2375_) as u8);
    v_res_2379_ =
        l_Lean_Elab_DefKind_opaque_elim(v_motive_2374_, v_t_boxed_2378_, v_h_2376_, v_opaque_2377_);
    crate::leanh::lean_dec(v_opaque_2377_);
    return v_res_2379_;
}
pub unsafe fn l_Lean_Elab_DefKind_abbrev_elim___redArg(
    mut v_abbrev_2380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_abbrev_2380_);
    return v_abbrev_2380_;
}
pub unsafe fn l_Lean_Elab_DefKind_abbrev_elim___redArg___boxed(
    mut v_abbrev_2381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2382_ = l_Lean_Elab_DefKind_abbrev_elim___redArg(v_abbrev_2381_);
    crate::leanh::lean_dec(v_abbrev_2381_);
    return v_res_2382_;
}
pub unsafe fn l_Lean_Elab_DefKind_abbrev_elim(
    mut v_motive_2383_: *mut crate::leanh::LeanObject,
    mut v_t_2384_: u8,
    mut v_h_2385_: *mut crate::leanh::LeanObject,
    mut v_abbrev_2386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_abbrev_2386_);
    return v_abbrev_2386_;
}
pub unsafe fn l_Lean_Elab_DefKind_abbrev_elim___boxed(
    mut v_motive_2387_: *mut crate::leanh::LeanObject,
    mut v_t_2388_: *mut crate::leanh::LeanObject,
    mut v_h_2389_: *mut crate::leanh::LeanObject,
    mut v_abbrev_2390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2391_: u8 = 0;
    let mut v_res_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2391_ = (crate::leanh::lean_unbox(v_t_2388_) as u8);
    v_res_2392_ =
        l_Lean_Elab_DefKind_abbrev_elim(v_motive_2387_, v_t_boxed_2391_, v_h_2389_, v_abbrev_2390_);
    crate::leanh::lean_dec(v_abbrev_2390_);
    return v_res_2392_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefKind_default() -> u8 {
    let mut v___x_2393_: u8 = 0;
    v___x_2393_ = 0;
    return v___x_2393_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefKind() -> u8 {
    let mut v___x_2394_: u8 = 0;
    v___x_2394_ = 0;
    return v___x_2394_;
}
pub unsafe fn l_Lean_Elab_instBEqDefKind_beq(mut v_x_2395_: u8, mut v_y_2396_: u8) -> u8 {
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: u8 = 0;
    v___x_2397_ = l_Lean_Elab_DefKind_ctorIdx(v_x_2395_);
    v___x_2398_ = l_Lean_Elab_DefKind_ctorIdx(v_y_2396_);
    v___x_2399_ = lean_nat_dec_eq(v___x_2397_, v___x_2398_);
    crate::leanh::lean_dec(v___x_2398_);
    crate::leanh::lean_dec(v___x_2397_);
    return v___x_2399_;
}
pub unsafe fn l_Lean_Elab_instBEqDefKind_beq___boxed(
    mut v_x_2400_: *mut crate::leanh::LeanObject,
    mut v_y_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_2402_: u8 = 0;
    let mut v_y_18__boxed_2403_: u8 = 0;
    let mut v_res_2404_: u8 = 0;
    let mut v_r_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2402_ = (crate::leanh::lean_unbox(v_x_2400_) as u8);
    v_y_18__boxed_2403_ = (crate::leanh::lean_unbox(v_y_2401_) as u8);
    v_res_2404_ = l_Lean_Elab_instBEqDefKind_beq(v_x_17__boxed_2402_, v_y_18__boxed_2403_);
    v_r_2405_ = crate::leanh::lean_box((v_res_2404_) as usize);
    return v_r_2405_;
}
pub unsafe fn l_Lean_Elab_DefKind_isTheorem(mut v_x_2408_: u8) -> u8 {
    if v_x_2408_ == 2 {
        let mut v___x_2409_: u8 = 0;
        v___x_2409_ = 1;
        return v___x_2409_;
    } else {
        let mut v___x_2410_: u8 = 0;
        v___x_2410_ = 0;
        return v___x_2410_;
    }
}
pub unsafe fn l_Lean_Elab_DefKind_isTheorem___boxed(
    mut v_x_2411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_2412_: u8 = 0;
    let mut v_res_2413_: u8 = 0;
    let mut v_r_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_2412_ = (crate::leanh::lean_unbox(v_x_2411_) as u8);
    v_res_2413_ = l_Lean_Elab_DefKind_isTheorem(v_x_21__boxed_2412_);
    v_r_2414_ = crate::leanh::lean_box((v_res_2413_) as usize);
    return v_r_2414_;
}
pub unsafe fn l_Lean_Elab_DefKind_isExample(mut v_x_2415_: u8) -> u8 {
    if v_x_2415_ == 3 {
        let mut v___x_2416_: u8 = 0;
        v___x_2416_ = 1;
        return v___x_2416_;
    } else {
        let mut v___x_2417_: u8 = 0;
        v___x_2417_ = 0;
        return v___x_2417_;
    }
}
pub unsafe fn l_Lean_Elab_DefKind_isExample___boxed(
    mut v_x_2418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_2419_: u8 = 0;
    let mut v_res_2420_: u8 = 0;
    let mut v_r_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_2419_ = (crate::leanh::lean_unbox(v_x_2418_) as u8);
    v_res_2420_ = l_Lean_Elab_DefKind_isExample(v_x_21__boxed_2419_);
    v_r_2421_ = crate::leanh::lean_box((v_res_2420_) as usize);
    return v_r_2421_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = crate::leanh::lean_box(0);
    v___x_2428_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__2;
    v___x_2429_ = l_Lean_Expr_const___override(v___x_2428_, v___x_2427_);
    return v___x_2429_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2430_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3_once
        ),
        _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__3,
    );
    v___x_2431_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2432_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0;
    v___x_2433_ = crate::leanh::lean_box(0);
    v___x_2434_ = crate::leanh::lean_box(0);
    v___x_2435_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2435_, 0, v___x_2434_);
    crate::leanh::lean_ctor_set(v___x_2435_, 1, v___x_2434_);
    crate::leanh::lean_ctor_set(v___x_2435_, 2, v___x_2433_);
    crate::leanh::lean_ctor_set(v___x_2435_, 3, v___x_2432_);
    crate::leanh::lean_ctor_set(v___x_2435_, 4, v___x_2431_);
    crate::leanh::lean_ctor_set(v___x_2435_, 5, v___x_2430_);
    return v___x_2435_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2436_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4_once
        ),
        _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__4,
    );
    return v___x_2436_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default;
    return v___x_2437_;
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(
    mut v_s_2438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSnapshot_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreSnaps_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSnapshot_2439_ = crate::leanh::lean_ctor_get(v_s_2438_, 0);
    v_moreSnaps_2440_ = crate::leanh::lean_ctor_get(v_s_2438_, 3);
    crate::leanh::lean_inc_ref(v_moreSnaps_2440_);
    crate::leanh::lean_inc_ref(v_toSnapshot_2439_);
    v___x_2441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2441_, 0, v_toSnapshot_2439_);
    crate::leanh::lean_ctor_set(v___x_2441_, 1, v_moreSnaps_2440_);
    return v___x_2441_;
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed(
    mut v_s_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(v_s_2442_);
    crate::leanh::lean_dec_ref(v_s_2442_);
    return v_res_2443_;
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(
    mut v_x_2446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2446_) == 0 {
        let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2447_ = l_Lean_Language_instInhabitedSnapshotTree_default;
        return v___x_2447_;
    } else {
        let mut v_val_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toSnapshot_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_moreSnaps_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2448_ = crate::leanh::lean_ctor_get(v_x_2446_, 0);
        v_toSnapshot_2449_ = crate::leanh::lean_ctor_get(v_val_2448_, 0);
        v_moreSnaps_2450_ = crate::leanh::lean_ctor_get(v_val_2448_, 3);
        crate::leanh::lean_inc_ref(v_moreSnaps_2450_);
        crate::leanh::lean_inc_ref(v_toSnapshot_2449_);
        v___x_2451_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2451_, 0, v_toSnapshot_2449_);
        crate::leanh::lean_ctor_set(v___x_2451_, 1, v_moreSnaps_2450_);
        return v___x_2451_;
    }
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(
    mut v_x_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(v_x_2452_);
    crate::leanh::lean_dec(v_x_2452_);
    return v_res_2453_;
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1(
    mut v___f_2457_: *mut crate::leanh::LeanObject,
    mut v_s_2458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSnapshot_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tacSnap_x3f_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodySnap_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreSnaps_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: u8 = 0;
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: u8 = 0;
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_2459_ = crate::leanh::lean_ctor_get(v_s_2458_, 0);
                crate::leanh::lean_inc_ref(v_toSnapshot_2459_);
                v_tacSnap_x3f_2460_ = crate::leanh::lean_ctor_get(v_s_2458_, 4);
                crate::leanh::lean_inc(v_tacSnap_x3f_2460_);
                v_bodySnap_2461_ = crate::leanh::lean_ctor_get(v_s_2458_, 6);
                crate::leanh::lean_inc_ref(v_bodySnap_2461_);
                v_moreSnaps_2462_ = crate::leanh::lean_ctor_get(v_s_2458_, 7);
                crate::leanh::lean_inc_ref(v_moreSnaps_2462_);
                crate::leanh::lean_dec_ref(v_s_2458_);
                if crate::leanh::lean_obj_tag(v_tacSnap_x3f_2460_) == 0 {
                    v___x_2475_ =
                        l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0;
                    v___y_2464_ = v___x_2475_;
                    state = 1;
                    continue;
                } else {
                    v_val_2476_ = crate::leanh::lean_ctor_get(v_tacSnap_x3f_2460_, 0);
                    crate::leanh::lean_inc(v_val_2476_);
                    crate::leanh::lean_dec_ref_known(v_tacSnap_x3f_2460_, 1);
                    v_stx_x3f_2477_ = crate::leanh::lean_ctor_get(v_val_2476_, 0);
                    crate::leanh::lean_inc(v_stx_x3f_2477_);
                    v_reportingRange_2478_ = crate::leanh::lean_ctor_get(v_val_2476_, 1);
                    crate::leanh::lean_inc(v_reportingRange_2478_);
                    v___x_2479_ =
                        l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1;
                    v___x_2480_ = 1;
                    v___x_2481_ = l_Lean_Language_SnapshotTask_map___redArg(
                        v_val_2476_,
                        v___x_2479_,
                        v_stx_x3f_2477_,
                        v_reportingRange_2478_,
                        v___x_2480_,
                    );
                    v___x_2482_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2483_ = lean_mk_empty_array_with_capacity(v___x_2482_);
                    v___x_2484_ = lean_array_push(v___x_2483_, v___x_2481_);
                    v___y_2464_ = v___x_2484_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_stx_x3f_2465_ = crate::leanh::lean_ctor_get(v_bodySnap_2461_, 0);
                crate::leanh::lean_inc(v_stx_x3f_2465_);
                v_reportingRange_2466_ = crate::leanh::lean_ctor_get(v_bodySnap_2461_, 1);
                crate::leanh::lean_inc(v_reportingRange_2466_);
                v___x_2467_ = 1;
                v___x_2468_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_bodySnap_2461_,
                    v___f_2457_,
                    v_stx_x3f_2465_,
                    v_reportingRange_2466_,
                    v___x_2467_,
                );
                v___x_2469_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2470_ = lean_mk_empty_array_with_capacity(v___x_2469_);
                v___x_2471_ = lean_array_push(v___x_2470_, v___x_2468_);
                v___x_2472_ = l_Array_append___redArg(v___y_2464_, v___x_2471_);
                crate::leanh::lean_dec_ref(v___x_2471_);
                v___x_2473_ = l_Array_append___redArg(v___x_2472_, v_moreSnaps_2462_);
                crate::leanh::lean_dec_ref(v_moreSnaps_2462_);
                v___x_2474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2474_, 0, v_toSnapshot_2459_);
                crate::leanh::lean_ctor_set(v___x_2474_, 1, v___x_2473_);
                return v___x_2474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(
    mut v___f_2498_: *mut crate::leanh::LeanObject,
    mut v_x_2499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSnapshot_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tacSnap_x3f_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bodySnap_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreSnaps_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: u8 = 0;
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2499_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2498_);
                    v___x_2500_ = l_Lean_Language_instInhabitedSnapshotTree_default;
                    return v___x_2500_;
                } else {
                    v_val_2501_ = crate::leanh::lean_ctor_get(v_x_2499_, 0);
                    crate::leanh::lean_inc(v_val_2501_);
                    crate::leanh::lean_dec_ref_known(v_x_2499_, 1);
                    v_toSnapshot_2502_ = crate::leanh::lean_ctor_get(v_val_2501_, 0);
                    crate::leanh::lean_inc_ref(v_toSnapshot_2502_);
                    v_tacSnap_x3f_2503_ = crate::leanh::lean_ctor_get(v_val_2501_, 4);
                    crate::leanh::lean_inc(v_tacSnap_x3f_2503_);
                    v_bodySnap_2504_ = crate::leanh::lean_ctor_get(v_val_2501_, 6);
                    crate::leanh::lean_inc_ref(v_bodySnap_2504_);
                    v_moreSnaps_2505_ = crate::leanh::lean_ctor_get(v_val_2501_, 7);
                    crate::leanh::lean_inc_ref(v_moreSnaps_2505_);
                    crate::leanh::lean_dec(v_val_2501_);
                    if crate::leanh::lean_obj_tag(v_tacSnap_x3f_2503_) == 0 {
                        v___x_2518_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__0;
                        v___y_2507_ = v___x_2518_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2519_ = crate::leanh::lean_ctor_get(v_tacSnap_x3f_2503_, 0);
                        crate::leanh::lean_inc(v_val_2519_);
                        crate::leanh::lean_dec_ref_known(v_tacSnap_x3f_2503_, 1);
                        v_stx_x3f_2520_ = crate::leanh::lean_ctor_get(v_val_2519_, 0);
                        crate::leanh::lean_inc(v_stx_x3f_2520_);
                        v_reportingRange_2521_ = crate::leanh::lean_ctor_get(v_val_2519_, 1);
                        crate::leanh::lean_inc(v_reportingRange_2521_);
                        v___x_2522_ = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1___closed__1;
                        v___x_2523_ = 1;
                        v___x_2524_ = l_Lean_Language_SnapshotTask_map___redArg(
                            v_val_2519_,
                            v___x_2522_,
                            v_stx_x3f_2520_,
                            v_reportingRange_2521_,
                            v___x_2523_,
                        );
                        v___x_2525_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2526_ = lean_mk_empty_array_with_capacity(v___x_2525_);
                        v___x_2527_ = lean_array_push(v___x_2526_, v___x_2524_);
                        v___y_2507_ = v___x_2527_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_stx_x3f_2508_ = crate::leanh::lean_ctor_get(v_bodySnap_2504_, 0);
                crate::leanh::lean_inc(v_stx_x3f_2508_);
                v_reportingRange_2509_ = crate::leanh::lean_ctor_get(v_bodySnap_2504_, 1);
                crate::leanh::lean_inc(v_reportingRange_2509_);
                v___x_2510_ = 1;
                v___x_2511_ = l_Lean_Language_SnapshotTask_map___redArg(
                    v_bodySnap_2504_,
                    v___f_2498_,
                    v_stx_x3f_2508_,
                    v_reportingRange_2509_,
                    v___x_2510_,
                );
                v___x_2512_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2513_ = lean_mk_empty_array_with_capacity(v___x_2512_);
                v___x_2514_ = lean_array_push(v___x_2513_, v___x_2511_);
                v___x_2515_ = l_Array_append___redArg(v___y_2507_, v___x_2514_);
                crate::leanh::lean_dec_ref(v___x_2514_);
                v___x_2516_ = l_Array_append___redArg(v___x_2515_, v_moreSnaps_2505_);
                crate::leanh::lean_dec_ref(v_moreSnaps_2505_);
                v___x_2517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2517_, 0, v_toSnapshot_2502_);
                crate::leanh::lean_ctor_set(v___x_2517_, 1, v___x_2516_);
                return v___x_2517_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(
    mut v___f_2528_: *mut crate::leanh::LeanObject,
    mut v_x_2529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_headerProcessedSnap_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x3f_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportingRange_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: u8 = 0;
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_headerProcessedSnap_2530_ = crate::leanh::lean_ctor_get(v_x_2529_, 1);
    crate::leanh::lean_inc_ref(v_headerProcessedSnap_2530_);
    crate::leanh::lean_dec_ref(v_x_2529_);
    v_stx_x3f_2531_ = crate::leanh::lean_ctor_get(v_headerProcessedSnap_2530_, 0);
    crate::leanh::lean_inc(v_stx_x3f_2531_);
    v_reportingRange_2532_ = crate::leanh::lean_ctor_get(v_headerProcessedSnap_2530_, 1);
    crate::leanh::lean_inc(v_reportingRange_2532_);
    v___x_2533_ = 1;
    v___x_2534_ = l_Lean_Language_SnapshotTask_map___redArg(
        v_headerProcessedSnap_2530_,
        v___f_2528_,
        v_stx_x3f_2531_,
        v_reportingRange_2532_,
        v___x_2533_,
    );
    return v___x_2534_;
}
pub unsafe fn l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2(
    mut v___f_2554_: *mut crate::leanh::LeanObject,
    mut v_s_2555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSnapshot_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defs_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2560_: u8 = 0;
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2562_: usize = 0;
    let mut v___x_2563_: usize = 0;
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSnapshot_2556_ = crate::leanh::lean_ctor_get(v_s_2555_, 0);
                v_defs_2557_ = crate::leanh::lean_ctor_get(v_s_2555_, 1);
                v_isSharedCheck_2568_ = (!crate::leanh::lean_is_exclusive(v_s_2555_)) as u8;
                if v_isSharedCheck_2568_ == 0 {
                    v___x_2559_ = v_s_2555_;
                    v_isShared_2560_ = v_isSharedCheck_2568_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_defs_2557_);
                    crate::leanh::lean_inc(v_toSnapshot_2556_);
                    crate::leanh::lean_dec(v_s_2555_);
                    v___x_2559_ = crate::leanh::lean_box(0);
                    v_isShared_2560_ = v_isSharedCheck_2568_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2561_ = l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2___closed__9;
                v_sz_2562_ = lean_array_size(v_defs_2557_);
                v___x_2563_ = 0usize;
                v___x_2564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2561_,
                    v___f_2554_,
                    v_sz_2562_,
                    v___x_2563_,
                    v_defs_2557_,
                );
                if v_isShared_2560_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2559_, 1, v___x_2564_);
                    v___x_2566_ = v___x_2559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_toSnapshot_2556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 1, v___x_2564_);
                    v___x_2566_ = v_reuseFailAlloc_2567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefView_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2576_ = crate::leanh::lean_box(0);
    v___x_2577_ = l_Lean_Elab_instInhabitedModifiers_default;
    v___x_2578_ = crate::leanh::lean_box(0);
    v___x_2579_ = 0;
    v___x_2580_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2580_, 0, v___x_2578_);
    crate::leanh::lean_ctor_set(v___x_2580_, 1, v___x_2578_);
    crate::leanh::lean_ctor_set(v___x_2580_, 2, v___x_2577_);
    crate::leanh::lean_ctor_set(v___x_2580_, 3, v___x_2578_);
    crate::leanh::lean_ctor_set(v___x_2580_, 4, v___x_2578_);
    crate::leanh::lean_ctor_set(v___x_2580_, 5, v___x_2576_);
    crate::leanh::lean_ctor_set(v___x_2580_, 6, v___x_2578_);
    crate::leanh::lean_ctor_set(v___x_2580_, 7, v___x_2576_);
    crate::leanh::lean_ctor_set(v___x_2580_, 8, v___x_2576_);
    crate::leanh::lean_ctor_set(v___x_2580_, 9, v___x_2576_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2580_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
        v___x_2579_,
    );
    return v___x_2580_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefView_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2581_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedDefView_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedDefView_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedDefView_default___closed__0,
    );
    return v___x_2581_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedDefView() -> *mut crate::leanh::LeanObject {
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2582_ = l_Lean_Elab_instInhabitedDefView_default;
    return v___x_2582_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(
    mut v_as_2586_: *mut crate::leanh::LeanObject,
    mut v_i_2587_: usize,
    mut v_stop_2588_: usize,
) -> u8 {
    let mut v___x_2589_: u8 = 0;
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: usize = 0;
    let mut v___x_2595_: usize = 0;
    let mut v___x_2597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2589_ = lean_usize_dec_eq(v_i_2587_, v_stop_2588_);
                if v___x_2589_ == 0 {
                    v___x_2590_ = lean_array_uget_borrowed(v_as_2586_, v_i_2587_);
                    v_name_2591_ = crate::leanh::lean_ctor_get(v___x_2590_, 0);
                    v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1;
                    v___x_2593_ = lean_name_eq(v_name_2591_, v___x_2592_);
                    if v___x_2593_ == 0 {
                        v___x_2594_ = 1usize;
                        v___x_2595_ = lean_usize_add(v_i_2587_, v___x_2594_);
                        v_i_2587_ = v___x_2595_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2593_;
                    }
                } else {
                    v___x_2597_ = 0;
                    return v___x_2597_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___boxed(
    mut v_as_2598_: *mut crate::leanh::LeanObject,
    mut v_i_2599_: *mut crate::leanh::LeanObject,
    mut v_stop_2600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2601_: usize = 0;
    let mut v_stop_boxed_2602_: usize = 0;
    let mut v_res_2603_: u8 = 0;
    let mut v_r_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2601_ = crate::leanh::lean_unbox_usize(v_i_2599_);
    crate::leanh::lean_dec(v_i_2599_);
    v_stop_boxed_2602_ = crate::leanh::lean_unbox_usize(v_stop_2600_);
    crate::leanh::lean_dec(v_stop_2600_);
    v_res_2603_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_as_2598_, v_i_boxed_2601_, v_stop_boxed_2602_);
    crate::leanh::lean_dec_ref(v_as_2598_);
    v_r_2604_ = crate::leanh::lean_box((v_res_2603_) as usize);
    return v_r_2604_;
}
pub unsafe fn l_Lean_Elab_DefView_isInstance(
    mut v_view_2605_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_modifiers_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: u8 = 0;
    v_modifiers_2606_ = crate::leanh::lean_ctor_get(v_view_2605_, 2);
    v_attrs_2607_ = crate::leanh::lean_ctor_get(v_modifiers_2606_, 2);
    v___x_2608_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2609_ = lean_array_get_size(v_attrs_2607_);
    v___x_2610_ = lean_nat_dec_lt(v___x_2608_, v___x_2609_);
    if v___x_2610_ == 0 {
        return v___x_2610_;
    } else {
        if v___x_2610_ == 0 {
            return v___x_2610_;
        } else {
            let mut v___x_2611_: usize = 0;
            let mut v___x_2612_: usize = 0;
            let mut v___x_2613_: u8 = 0;
            v___x_2611_ = 0usize;
            v___x_2612_ = lean_usize_of_nat(v___x_2609_);
            v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0(v_attrs_2607_, v___x_2611_, v___x_2612_);
            return v___x_2613_;
        }
    }
}
pub unsafe fn l_Lean_Elab_DefView_isInstance___boxed(
    mut v_view_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2615_: u8 = 0;
    let mut v_r_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2615_ = l_Lean_Elab_DefView_isInstance(v_view_2614_);
    crate::leanh::lean_dec_ref(v_view_2614_);
    v_r_2616_ = crate::leanh::lean_box((v_res_2615_) as usize);
    return v_r_2616_;
}
pub unsafe fn l_Lean_Elab_DefView_markDefEq___lam__0(
    mut v_x_2620_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: u8 = 0;
    v_name_2621_ = crate::leanh::lean_ctor_get(v_x_2620_, 0);
    v___x_2622_ = l_Lean_Elab_DefView_markDefEq___lam__0___closed__1;
    v___x_2623_ = lean_name_eq(v_name_2621_, v___x_2622_);
    if v___x_2623_ == 0 {
        let mut v___x_2624_: u8 = 0;
        v___x_2624_ = 1;
        return v___x_2624_;
    } else {
        let mut v___x_2625_: u8 = 0;
        v___x_2625_ = 0;
        return v___x_2625_;
    }
}
pub unsafe fn l_Lean_Elab_DefView_markDefEq___lam__0___boxed(
    mut v_x_2626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2627_: u8 = 0;
    let mut v_r_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Lean_Elab_DefView_markDefEq___lam__0(v_x_2626_);
    crate::leanh::lean_dec_ref(v_x_2626_);
    v_r_2628_ = crate::leanh::lean_box((v_res_2627_) as usize);
    return v_r_2628_;
}
pub unsafe fn l_Lean_Elab_DefView_markDefEq(
    mut v_view_2634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_2635_: u8 = 0;
    let mut v_ref_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerRef_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifiers_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declId_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_x3f_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_headerSnap_x3f_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deriving_x3f_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2648_: u8 = 0;
    let mut v___f_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_2635_ = crate::leanh::lean_ctor_get_uint8(
                    v_view_2634_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_ref_2636_ = crate::leanh::lean_ctor_get(v_view_2634_, 0);
                v_headerRef_2637_ = crate::leanh::lean_ctor_get(v_view_2634_, 1);
                v_modifiers_2638_ = crate::leanh::lean_ctor_get(v_view_2634_, 2);
                v_declId_2639_ = crate::leanh::lean_ctor_get(v_view_2634_, 3);
                v_binders_2640_ = crate::leanh::lean_ctor_get(v_view_2634_, 4);
                v_type_x3f_2641_ = crate::leanh::lean_ctor_get(v_view_2634_, 5);
                v_value_2642_ = crate::leanh::lean_ctor_get(v_view_2634_, 6);
                v_docString_x3f_2643_ = crate::leanh::lean_ctor_get(v_view_2634_, 7);
                v_headerSnap_x3f_2644_ = crate::leanh::lean_ctor_get(v_view_2634_, 8);
                v_deriving_x3f_2645_ = crate::leanh::lean_ctor_get(v_view_2634_, 9);
                v_isSharedCheck_2656_ = (!crate::leanh::lean_is_exclusive(v_view_2634_)) as u8;
                if v_isSharedCheck_2656_ == 0 {
                    v___x_2647_ = v_view_2634_;
                    v_isShared_2648_ = v_isSharedCheck_2656_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_deriving_x3f_2645_);
                    crate::leanh::lean_inc(v_headerSnap_x3f_2644_);
                    crate::leanh::lean_inc(v_docString_x3f_2643_);
                    crate::leanh::lean_inc(v_value_2642_);
                    crate::leanh::lean_inc(v_type_x3f_2641_);
                    crate::leanh::lean_inc(v_binders_2640_);
                    crate::leanh::lean_inc(v_declId_2639_);
                    crate::leanh::lean_inc(v_modifiers_2638_);
                    crate::leanh::lean_inc(v_headerRef_2637_);
                    crate::leanh::lean_inc(v_ref_2636_);
                    crate::leanh::lean_dec(v_view_2634_);
                    v___x_2647_ = crate::leanh::lean_box(0);
                    v_isShared_2648_ = v_isSharedCheck_2656_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2649_ = l_Lean_Elab_DefView_markDefEq___closed__0;
                v___x_2650_ = l_Lean_Elab_Modifiers_filterAttrs(v_modifiers_2638_, v___f_2649_);
                v___x_2651_ = l_Lean_Elab_DefView_markDefEq___closed__1;
                v___x_2652_ = l_Lean_Elab_Modifiers_addFirstAttr(v___x_2650_, v___x_2651_);
                if v_isShared_2648_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2647_, 2, v___x_2652_);
                    v___x_2654_ = v___x_2647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2655_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_ref_2636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_headerRef_2637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 2, v___x_2652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_declId_2639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 4, v_binders_2640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 5, v_type_x3f_2641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 6, v_value_2642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 7, v_docString_x3f_2643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 8, v_headerSnap_x3f_2644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 9, v_deriving_x3f_2645_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2655_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_kind_2635_,
                    );
                    v___x_2654_ = v_reuseFailAlloc_2655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfAbbrev(
    mut v_modifiers_2674_: *mut crate::leanh::LeanObject,
    mut v_stx_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifiers_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifiers_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: u8 = 0;
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2676_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2677_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2676_);
    v___x_2678_ = l_Lean_Elab_expandOptDeclSig(v___x_2677_);
    crate::leanh::lean_dec(v___x_2677_);
    v_fst_2679_ = crate::leanh::lean_ctor_get(v___x_2678_, 0);
    crate::leanh::lean_inc(v_fst_2679_);
    v_snd_2680_ = crate::leanh::lean_ctor_get(v___x_2678_, 1);
    crate::leanh::lean_inc(v_snd_2680_);
    crate::leanh::lean_dec_ref(v___x_2678_);
    v___x_2681_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2;
    v_modifiers_2682_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_2674_, v___x_2681_);
    v___x_2683_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__5;
    v_modifiers_2684_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_2682_, v___x_2683_);
    v_docString_x3f_2685_ = crate::leanh::lean_ctor_get(v_modifiers_2684_, 1);
    crate::leanh::lean_inc(v_docString_x3f_2685_);
    v___x_2686_ = 5;
    v___x_2687_ = l_Lean_Syntax_getArgs(v_stx_2675_);
    v___x_2688_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2689_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2690_ = l_Array_toSubarray___redArg(v___x_2687_, v___x_2689_, v___x_2688_);
    v___x_2691_ = l_Subarray_copy___redArg(v___x_2690_);
    v___x_2692_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
    v___x_2693_ = crate::leanh::lean_box(2);
    v___x_2694_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2694_, 0, v___x_2693_);
    crate::leanh::lean_ctor_set(v___x_2694_, 1, v___x_2692_);
    crate::leanh::lean_ctor_set(v___x_2694_, 2, v___x_2691_);
    v___x_2695_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2696_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2695_);
    v___x_2697_ = l_Lean_Syntax_getArg(v_stx_2675_, v___x_2688_);
    v___x_2698_ = crate::leanh::lean_box(0);
    v___x_2699_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2699_, 0, v_stx_2675_);
    crate::leanh::lean_ctor_set(v___x_2699_, 1, v___x_2694_);
    crate::leanh::lean_ctor_set(v___x_2699_, 2, v_modifiers_2684_);
    crate::leanh::lean_ctor_set(v___x_2699_, 3, v___x_2696_);
    crate::leanh::lean_ctor_set(v___x_2699_, 4, v_fst_2679_);
    crate::leanh::lean_ctor_set(v___x_2699_, 5, v_snd_2680_);
    crate::leanh::lean_ctor_set(v___x_2699_, 6, v___x_2697_);
    crate::leanh::lean_ctor_set(v___x_2699_, 7, v_docString_x3f_2685_);
    crate::leanh::lean_ctor_set(v___x_2699_, 8, v___x_2698_);
    crate::leanh::lean_ctor_set(v___x_2699_, 9, v___x_2698_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2699_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
        v___x_2686_,
    );
    return v___x_2699_;
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfDef(
    mut v_modifiers_2700_: *mut crate::leanh::LeanObject,
    mut v_stx_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: u8 = 0;
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: u8 = 0;
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2702_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2703_ = l_Lean_Syntax_getArg(v_stx_2701_, v___x_2702_);
                v___x_2704_ = l_Lean_Elab_expandOptDeclSig(v___x_2703_);
                crate::leanh::lean_dec(v___x_2703_);
                v_fst_2705_ = crate::leanh::lean_ctor_get(v___x_2704_, 0);
                crate::leanh::lean_inc(v_fst_2705_);
                v_snd_2706_ = crate::leanh::lean_ctor_get(v___x_2704_, 1);
                crate::leanh::lean_inc(v_snd_2706_);
                crate::leanh::lean_dec_ref(v___x_2704_);
                v___x_2724_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2725_ = l_Lean_Syntax_getArg(v_stx_2701_, v___x_2724_);
                v___x_2726_ = l_Lean_Syntax_isNone(v___x_2725_);
                if v___x_2726_ == 0 {
                    v___x_2727_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2728_ = l_Lean_Syntax_getArg(v___x_2725_, v___x_2727_);
                    crate::leanh::lean_dec(v___x_2725_);
                    v___x_2729_ = l_Lean_Syntax_getSepArgs(v___x_2728_);
                    crate::leanh::lean_dec(v___x_2728_);
                    v___x_2730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2730_, 0, v___x_2729_);
                    v___y_2708_ = v___x_2730_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2725_);
                    v___x_2731_ = crate::leanh::lean_box(0);
                    v___y_2708_ = v___x_2731_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_docString_x3f_2709_ = crate::leanh::lean_ctor_get(v_modifiers_2700_, 1);
                crate::leanh::lean_inc(v_docString_x3f_2709_);
                v___x_2710_ = 0;
                v___x_2711_ = l_Lean_Syntax_getArgs(v_stx_2701_);
                v___x_2712_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2713_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2714_ = l_Array_toSubarray___redArg(v___x_2711_, v___x_2713_, v___x_2712_);
                v___x_2715_ = l_Subarray_copy___redArg(v___x_2714_);
                v___x_2716_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_2717_ = crate::leanh::lean_box(2);
                v___x_2718_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2718_, 0, v___x_2717_);
                crate::leanh::lean_ctor_set(v___x_2718_, 1, v___x_2716_);
                crate::leanh::lean_ctor_set(v___x_2718_, 2, v___x_2715_);
                v___x_2719_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2720_ = l_Lean_Syntax_getArg(v_stx_2701_, v___x_2719_);
                v___x_2721_ = l_Lean_Syntax_getArg(v_stx_2701_, v___x_2712_);
                v___x_2722_ = crate::leanh::lean_box(0);
                v___x_2723_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2723_, 0, v_stx_2701_);
                crate::leanh::lean_ctor_set(v___x_2723_, 1, v___x_2718_);
                crate::leanh::lean_ctor_set(v___x_2723_, 2, v_modifiers_2700_);
                crate::leanh::lean_ctor_set(v___x_2723_, 3, v___x_2720_);
                crate::leanh::lean_ctor_set(v___x_2723_, 4, v_fst_2705_);
                crate::leanh::lean_ctor_set(v___x_2723_, 5, v_snd_2706_);
                crate::leanh::lean_ctor_set(v___x_2723_, 6, v___x_2721_);
                crate::leanh::lean_ctor_set(v___x_2723_, 7, v_docString_x3f_2709_);
                crate::leanh::lean_ctor_set(v___x_2723_, 8, v___x_2722_);
                crate::leanh::lean_ctor_set(v___x_2723_, 9, v___y_2708_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2723_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    v___x_2710_,
                );
                return v___x_2723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfTheorem(
    mut v_modifiers_2732_: *mut crate::leanh::LeanObject,
    mut v_stx_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: u8 = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2734_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2735_ = l_Lean_Syntax_getArg(v_stx_2733_, v___x_2734_);
    v___x_2736_ = l_Lean_Elab_expandDeclSig(v___x_2735_);
    crate::leanh::lean_dec(v___x_2735_);
    v_fst_2737_ = crate::leanh::lean_ctor_get(v___x_2736_, 0);
    crate::leanh::lean_inc(v_fst_2737_);
    v_snd_2738_ = crate::leanh::lean_ctor_get(v___x_2736_, 1);
    crate::leanh::lean_inc(v_snd_2738_);
    crate::leanh::lean_dec_ref(v___x_2736_);
    v_docString_x3f_2739_ = crate::leanh::lean_ctor_get(v_modifiers_2732_, 1);
    crate::leanh::lean_inc(v_docString_x3f_2739_);
    v___x_2740_ = 2;
    v___x_2741_ = l_Lean_Syntax_getArgs(v_stx_2733_);
    v___x_2742_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2743_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2744_ = l_Array_toSubarray___redArg(v___x_2741_, v___x_2743_, v___x_2742_);
    v___x_2745_ = l_Subarray_copy___redArg(v___x_2744_);
    v___x_2746_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
    v___x_2747_ = crate::leanh::lean_box(2);
    v___x_2748_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2748_, 0, v___x_2747_);
    crate::leanh::lean_ctor_set(v___x_2748_, 1, v___x_2746_);
    crate::leanh::lean_ctor_set(v___x_2748_, 2, v___x_2745_);
    v___x_2749_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2750_ = l_Lean_Syntax_getArg(v_stx_2733_, v___x_2749_);
    v___x_2751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2751_, 0, v_snd_2738_);
    v___x_2752_ = l_Lean_Syntax_getArg(v_stx_2733_, v___x_2742_);
    v___x_2753_ = crate::leanh::lean_box(0);
    v___x_2754_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2754_, 0, v_stx_2733_);
    crate::leanh::lean_ctor_set(v___x_2754_, 1, v___x_2748_);
    crate::leanh::lean_ctor_set(v___x_2754_, 2, v_modifiers_2732_);
    crate::leanh::lean_ctor_set(v___x_2754_, 3, v___x_2750_);
    crate::leanh::lean_ctor_set(v___x_2754_, 4, v_fst_2737_);
    crate::leanh::lean_ctor_set(v___x_2754_, 5, v___x_2751_);
    crate::leanh::lean_ctor_set(v___x_2754_, 6, v___x_2752_);
    crate::leanh::lean_ctor_set(v___x_2754_, 7, v_docString_x3f_2739_);
    crate::leanh::lean_ctor_set(v___x_2754_, 8, v___x_2753_);
    crate::leanh::lean_ctor_set(v___x_2754_, 9, v___x_2753_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2754_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
        v___x_2740_,
    );
    return v___x_2754_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(
    mut v___y_2755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2757_ = lean_st_ref_get(v___y_2755_);
    v_env_2758_ = crate::leanh::lean_ctor_get(v___x_2757_, 0);
    crate::leanh::lean_inc_ref(v_env_2758_);
    crate::leanh::lean_dec(v___x_2757_);
    v___x_2759_ = l_Lean_Environment_header(v_env_2758_);
    crate::leanh::lean_dec_ref(v_env_2758_);
    v_mainModule_2760_ = crate::leanh::lean_ctor_get(v___x_2759_, 0);
    crate::leanh::lean_inc(v_mainModule_2760_);
    crate::leanh::lean_dec_ref(v___x_2759_);
    v___x_2761_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2761_, 0, v_mainModule_2760_);
    return v___x_2761_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg___boxed(
    mut v___y_2762_: *mut crate::leanh::LeanObject,
    mut v___y_2763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2764_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(
            v___y_2762_,
        );
    crate::leanh::lean_dec(v___y_2762_);
    return v_res_2764_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(
    mut v___y_2765_: *mut crate::leanh::LeanObject,
    mut v___y_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2768_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(
            v___y_2766_,
        );
    return v___x_2768_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___boxed(
    mut v___y_2769_: *mut crate::leanh::LeanObject,
    mut v___y_2770_: *mut crate::leanh::LeanObject,
    mut v___y_2771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2(
        v___y_2769_,
        v___y_2770_,
    );
    crate::leanh::lean_dec(v___y_2770_);
    crate::leanh::lean_dec_ref(v___y_2769_);
    return v_res_2772_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2778_ = l_Lean_maxRecDepthErrorMessage;
    v___x_2779_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2779_, 0, v___x_2778_);
    return v___x_2779_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2780_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__3);
    v___x_2781_ = l_Lean_MessageData_ofFormat(v___x_2780_);
    return v___x_2781_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2782_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__4);
    v___x_2783_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__2;
    v___x_2784_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2784_, 0, v___x_2783_);
    crate::leanh::lean_ctor_set(v___x_2784_, 1, v___x_2782_);
    return v___x_2784_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(
    mut v_ref_2785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2787_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___closed__5);
    v___x_2788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2788_, 0, v_ref_2785_);
    crate::leanh::lean_ctor_set(v___x_2788_, 1, v___x_2787_);
    v___x_2789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2789_, 0, v___x_2788_);
    return v___x_2789_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg___boxed(
    mut v_ref_2790_: *mut crate::leanh::LeanObject,
    mut v___y_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_2790_);
    return v_res_2792_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(
    mut v_x_2793_: *mut crate::leanh::LeanObject,
    mut v___y_2794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2793_) == 0 {
        let mut v_a_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2795_ = crate::leanh::lean_ctor_get(v_x_2793_, 0);
        crate::leanh::lean_inc(v_a_2795_);
        v___x_2796_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2796_, 0, v_a_2795_);
        crate::leanh::lean_ctor_set(v___x_2796_, 1, v___y_2794_);
        return v___x_2796_;
    } else {
        let mut v_a_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2797_ = crate::leanh::lean_ctor_get(v_x_2793_, 0);
        crate::leanh::lean_inc(v_a_2797_);
        v___x_2798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2798_, 0, v_a_2797_);
        crate::leanh::lean_ctor_set(v___x_2798_, 1, v___y_2794_);
        return v___x_2798_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg___boxed(
    mut v_x_2799_: *mut crate::leanh::LeanObject,
    mut v___y_2800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2801_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_2799_, v___y_2800_);
    crate::leanh::lean_dec_ref(v_x_2799_);
    return v_res_2801_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(
    mut v_env_2802_: *mut crate::leanh::LeanObject,
    mut v_stx_2803_: *mut crate::leanh::LeanObject,
    mut v___y_2804_: *mut crate::leanh::LeanObject,
    mut v___y_2805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_unused_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2821_: u8 = 0;
    let mut v_snd_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2832_: u8 = 0;
    let mut v_a_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2845_: u8 = 0;
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut v_a_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2851_: u8 = 0;
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2806_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_2802_,
                    v_stx_2803_,
                    v___y_2804_,
                    v___y_2805_,
                );
                if crate::leanh::lean_obj_tag(v___x_2806_) == 0 {
                    v_a_2807_ = crate::leanh::lean_ctor_get(v___x_2806_, 0);
                    crate::leanh::lean_inc(v_a_2807_);
                    if crate::leanh::lean_obj_tag(v_a_2807_) == 0 {
                        v_a_2808_ = crate::leanh::lean_ctor_get(v___x_2806_, 1);
                        v_isSharedCheck_2816_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2806_)) as u8;
                        if v_isSharedCheck_2816_ == 0 {
                            v_unused_2817_ = crate::leanh::lean_ctor_get(v___x_2806_, 0);
                            crate::leanh::lean_dec(v_unused_2817_);
                            v___x_2810_ = v___x_2806_;
                            v_isShared_2811_ = v_isSharedCheck_2816_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2808_);
                            crate::leanh::lean_dec(v___x_2806_);
                            v___x_2810_ = crate::leanh::lean_box(0);
                            v_isShared_2811_ = v_isSharedCheck_2816_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_2818_ = crate::leanh::lean_ctor_get(v_a_2807_, 0);
                        v_isSharedCheck_2846_ = (!crate::leanh::lean_is_exclusive(v_a_2807_)) as u8;
                        if v_isSharedCheck_2846_ == 0 {
                            v___x_2820_ = v_a_2807_;
                            v_isShared_2821_ = v_isSharedCheck_2846_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2818_);
                            crate::leanh::lean_dec(v_a_2807_);
                            v___x_2820_ = crate::leanh::lean_box(0);
                            v_isShared_2821_ = v_isSharedCheck_2846_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2847_ = crate::leanh::lean_ctor_get(v___x_2806_, 0);
                    v_a_2848_ = crate::leanh::lean_ctor_get(v___x_2806_, 1);
                    v_isSharedCheck_2855_ = (!crate::leanh::lean_is_exclusive(v___x_2806_)) as u8;
                    if v_isSharedCheck_2855_ == 0 {
                        v___x_2850_ = v___x_2806_;
                        v_isShared_2851_ = v_isSharedCheck_2855_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2848_);
                        crate::leanh::lean_inc(v_a_2847_);
                        crate::leanh::lean_dec(v___x_2806_);
                        v___x_2850_ = crate::leanh::lean_box(0);
                        v_isShared_2851_ = v_isSharedCheck_2855_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2812_ = crate::leanh::lean_box(0);
                if v_isShared_2811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2810_, 0, v___x_2812_);
                    v___x_2814_ = v___x_2810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_a_2808_);
                    v___x_2814_ = v_reuseFailAlloc_2815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2814_;
            }
            3 => {
                v_snd_2822_ = crate::leanh::lean_ctor_get(v_val_2818_, 1);
                crate::leanh::lean_inc(v_snd_2822_);
                crate::leanh::lean_dec(v_val_2818_);
                if crate::leanh::lean_obj_tag(v_snd_2822_) == 0 {
                    crate::leanh::lean_del_object(v___x_2820_);
                    v_a_2823_ = crate::leanh::lean_ctor_get(v___x_2806_, 1);
                    crate::leanh::lean_inc(v_a_2823_);
                    crate::leanh::lean_dec_ref_known(v___x_2806_, 2);
                    v_a_2824_ = crate::leanh::lean_ctor_get(v_snd_2822_, 0);
                    v_isSharedCheck_2832_ = (!crate::leanh::lean_is_exclusive(v_snd_2822_)) as u8;
                    if v_isSharedCheck_2832_ == 0 {
                        v___x_2826_ = v_snd_2822_;
                        v_isShared_2827_ = v_isSharedCheck_2832_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2824_);
                        crate::leanh::lean_dec(v_snd_2822_);
                        v___x_2826_ = crate::leanh::lean_box(0);
                        v_isShared_2827_ = v_isSharedCheck_2832_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2833_ = crate::leanh::lean_ctor_get(v___x_2806_, 1);
                    crate::leanh::lean_inc(v_a_2833_);
                    crate::leanh::lean_dec_ref_known(v___x_2806_, 2);
                    v_a_2834_ = crate::leanh::lean_ctor_get(v_snd_2822_, 0);
                    v_isSharedCheck_2845_ = (!crate::leanh::lean_is_exclusive(v_snd_2822_)) as u8;
                    if v_isSharedCheck_2845_ == 0 {
                        v___x_2836_ = v_snd_2822_;
                        v_isShared_2837_ = v_isSharedCheck_2845_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2834_);
                        crate::leanh::lean_dec(v_snd_2822_);
                        v___x_2836_ = crate::leanh::lean_box(0);
                        v_isShared_2837_ = v_isSharedCheck_2845_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2827_ == 0 {
                    v___x_2829_ = v___x_2826_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2824_);
                    v___x_2829_ = v_reuseFailAlloc_2831_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2830_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_2829_, v_a_2823_);
                crate::leanh::lean_dec_ref(v___x_2829_);
                return v___x_2830_;
            }
            6 => {
                if v_isShared_2821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2820_, 0, v_a_2834_);
                    v___x_2839_ = v___x_2820_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2834_);
                    v___x_2839_ = v_reuseFailAlloc_2844_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2836_, 0, v___x_2839_);
                    v___x_2841_ = v___x_2836_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2839_);
                    v___x_2841_ = v_reuseFailAlloc_2843_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2842_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v___x_2841_, v_a_2833_);
                crate::leanh::lean_dec_ref(v___x_2841_);
                return v___x_2842_;
            }
            9 => {
                if v_isShared_2851_ == 0 {
                    v___x_2853_ = v___x_2850_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2854_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_a_2848_);
                    v___x_2853_ = v_reuseFailAlloc_2854_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed(
    mut v_env_2856_: *mut crate::leanh::LeanObject,
    mut v_stx_2857_: *mut crate::leanh::LeanObject,
    mut v___y_2858_: *mut crate::leanh::LeanObject,
    mut v___y_2859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2860_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1(v_env_2856_, v_stx_2857_, v___y_2858_, v___y_2859_);
    crate::leanh::lean_dec_ref(v___y_2858_);
    return v_res_2860_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(
    mut v_env_2861_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_2862_: *mut crate::leanh::LeanObject,
    mut v_openDecls_2863_: *mut crate::leanh::LeanObject,
    mut v_n_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
    mut v___y_2866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2867_ = l_Lean_ResolveName_resolveNamespace(
        v_env_2861_,
        v_currNamespace_2862_,
        v_openDecls_2863_,
        v_n_2864_,
    );
    v___x_2868_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2868_, 0, v___x_2867_);
    crate::leanh::lean_ctor_set(v___x_2868_, 1, v___y_2866_);
    return v___x_2868_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed(
    mut v_env_2869_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_2870_: *mut crate::leanh::LeanObject,
    mut v_openDecls_2871_: *mut crate::leanh::LeanObject,
    mut v_n_2872_: *mut crate::leanh::LeanObject,
    mut v___y_2873_: *mut crate::leanh::LeanObject,
    mut v___y_2874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2875_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3(v_env_2869_, v_currNamespace_2870_, v_openDecls_2871_, v_n_2872_, v___y_2873_, v___y_2874_);
    crate::leanh::lean_dec_ref(v___y_2873_);
    return v_res_2875_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(
    mut v_currNamespace_2876_: *mut crate::leanh::LeanObject,
    mut v___y_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2879_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2879_, 0, v_currNamespace_2876_);
    crate::leanh::lean_ctor_set(v___x_2879_, 1, v___y_2878_);
    return v___x_2879_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed(
    mut v_currNamespace_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2883_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2(v_currNamespace_2880_, v___y_2881_, v___y_2882_);
    crate::leanh::lean_dec_ref(v___y_2881_);
    return v_res_2883_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2884_ = crate::leanh::lean_box(0);
    v___x_2885_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2886_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2886_, 0, v___x_2885_);
    crate::leanh::lean_ctor_set(v___x_2886_, 1, v___x_2884_);
    return v___x_2886_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2888_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___closed__0);
    v___x_2889_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2889_, 0, v___x_2888_);
    return v___x_2889_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg___boxed(
    mut v___y_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2891_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
    return v_res_2891_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2892_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2892_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2893_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__0);
    v___x_2894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2894_, 0, v___x_2893_);
    return v___x_2894_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2895_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
    v___x_2896_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2897_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2897_, 0, v___x_2896_);
    crate::leanh::lean_ctor_set(v___x_2897_, 1, v___x_2896_);
    crate::leanh::lean_ctor_set(v___x_2897_, 2, v___x_2896_);
    crate::leanh::lean_ctor_set(v___x_2897_, 3, v___x_2896_);
    crate::leanh::lean_ctor_set(v___x_2897_, 4, v___x_2895_);
    crate::leanh::lean_ctor_set(v___x_2897_, 5, v___x_2895_);
    crate::leanh::lean_ctor_set(v___x_2897_, 6, v___x_2895_);
    crate::leanh::lean_ctor_set(v___x_2897_, 7, v___x_2895_);
    crate::leanh::lean_ctor_set(v___x_2897_, 8, v___x_2895_);
    crate::leanh::lean_ctor_set(v___x_2897_, 9, v___x_2895_);
    return v___x_2897_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2898_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2899_ = lean_mk_empty_array_with_capacity(v___x_2898_);
    v___x_2900_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2900_, 0, v___x_2899_);
    return v___x_2900_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2901_: usize = 0;
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2901_ = 5usize;
    v___x_2902_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2903_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2904_ = lean_mk_empty_array_with_capacity(v___x_2903_);
    v___x_2905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__3);
    v___x_2906_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2906_, 0, v___x_2905_);
    crate::leanh::lean_ctor_set(v___x_2906_, 1, v___x_2904_);
    crate::leanh::lean_ctor_set(v___x_2906_, 2, v___x_2902_);
    crate::leanh::lean_ctor_set(v___x_2906_, 3, v___x_2902_);
    crate::leanh::lean_ctor_set_usize(v___x_2906_, 4, v___x_2901_);
    return v___x_2906_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2907_ = crate::leanh::lean_box(1);
    v___x_2908_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__4);
    v___x_2909_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__1);
    v___x_2910_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_2909_);
    crate::leanh::lean_ctor_set(v___x_2910_, 1, v___x_2908_);
    crate::leanh::lean_ctor_set(v___x_2910_, 2, v___x_2907_);
    return v___x_2910_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(
    mut v_msgData_2911_: *mut crate::leanh::LeanObject,
    mut v___y_2912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = lean_st_ref_get(v___y_2912_);
    v_env_2915_ = crate::leanh::lean_ctor_get(v___x_2914_, 0);
    crate::leanh::lean_inc_ref(v_env_2915_);
    crate::leanh::lean_dec(v___x_2914_);
    v___x_2916_ = lean_st_ref_get(v___y_2912_);
    v_scopes_2917_ = crate::leanh::lean_ctor_get(v___x_2916_, 2);
    crate::leanh::lean_inc(v_scopes_2917_);
    crate::leanh::lean_dec(v___x_2916_);
    v___x_2918_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2919_ = l_List_head_x21___redArg(v___x_2918_, v_scopes_2917_);
    crate::leanh::lean_dec(v_scopes_2917_);
    v_opts_2920_ = crate::leanh::lean_ctor_get(v___x_2919_, 1);
    crate::leanh::lean_inc_ref(v_opts_2920_);
    crate::leanh::lean_dec(v___x_2919_);
    v___x_2921_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__2);
    v___x_2922_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___closed__5);
    v___x_2923_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2923_, 0, v_env_2915_);
    crate::leanh::lean_ctor_set(v___x_2923_, 1, v___x_2921_);
    crate::leanh::lean_ctor_set(v___x_2923_, 2, v___x_2922_);
    crate::leanh::lean_ctor_set(v___x_2923_, 3, v_opts_2920_);
    v___x_2924_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2924_, 0, v___x_2923_);
    crate::leanh::lean_ctor_set(v___x_2924_, 1, v_msgData_2911_);
    v___x_2925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2925_, 0, v___x_2924_);
    return v___x_2925_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg___boxed(
    mut v_msgData_2926_: *mut crate::leanh::LeanObject,
    mut v___y_2927_: *mut crate::leanh::LeanObject,
    mut v___y_2928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2929_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_2926_, v___y_2927_);
    crate::leanh::lean_dec(v___y_2927_);
    return v_res_2929_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0()
-> f64 {
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: f64 = 0.0;
    v___x_2930_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2931_ = lean_float_of_nat(v___x_2930_);
    return v___x_2931_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(
    mut v_cls_2935_: *mut crate::leanh::LeanObject,
    mut v_msg_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2946_: u8 = 0;
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2961_: u8 = 0;
    let mut v_tid_2962_: u64 = 0;
    let mut v_traces_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: f64 = 0.0;
    let mut v___x_2969_: u8 = 0;
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut v_isSharedCheck_2988_: u8 = 0;
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_a_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2993_: u8 = 0;
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2940_ = l_Lean_Elab_Command_getRef___redArg(v___y_2937_);
                if crate::leanh::lean_obj_tag(v___x_2940_) == 0 {
                    v_a_2941_ = crate::leanh::lean_ctor_get(v___x_2940_, 0);
                    crate::leanh::lean_inc(v_a_2941_);
                    crate::leanh::lean_dec_ref_known(v___x_2940_, 1);
                    v___x_2942_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_2936_, v___y_2938_);
                    v_a_2943_ = crate::leanh::lean_ctor_get(v___x_2942_, 0);
                    v_isSharedCheck_2989_ = (!crate::leanh::lean_is_exclusive(v___x_2942_)) as u8;
                    if v_isSharedCheck_2989_ == 0 {
                        v___x_2945_ = v___x_2942_;
                        v_isShared_2946_ = v_isSharedCheck_2989_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2943_);
                        crate::leanh::lean_dec(v___x_2942_);
                        v___x_2945_ = crate::leanh::lean_box(0);
                        v_isShared_2946_ = v_isSharedCheck_2989_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_2936_);
                    crate::leanh::lean_dec(v_cls_2935_);
                    v_a_2990_ = crate::leanh::lean_ctor_get(v___x_2940_, 0);
                    v_isSharedCheck_2997_ = (!crate::leanh::lean_is_exclusive(v___x_2940_)) as u8;
                    if v_isSharedCheck_2997_ == 0 {
                        v___x_2992_ = v___x_2940_;
                        v_isShared_2993_ = v_isSharedCheck_2997_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2990_);
                        crate::leanh::lean_dec(v___x_2940_);
                        v___x_2992_ = crate::leanh::lean_box(0);
                        v_isShared_2993_ = v_isSharedCheck_2997_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2947_ = lean_st_ref_take(v___y_2938_);
                v_traceState_2948_ = crate::leanh::lean_ctor_get(v___x_2947_, 9);
                v_env_2949_ = crate::leanh::lean_ctor_get(v___x_2947_, 0);
                v_messages_2950_ = crate::leanh::lean_ctor_get(v___x_2947_, 1);
                v_scopes_2951_ = crate::leanh::lean_ctor_get(v___x_2947_, 2);
                v_usedQuotCtxts_2952_ = crate::leanh::lean_ctor_get(v___x_2947_, 3);
                v_nextMacroScope_2953_ = crate::leanh::lean_ctor_get(v___x_2947_, 4);
                v_maxRecDepth_2954_ = crate::leanh::lean_ctor_get(v___x_2947_, 5);
                v_ngen_2955_ = crate::leanh::lean_ctor_get(v___x_2947_, 6);
                v_auxDeclNGen_2956_ = crate::leanh::lean_ctor_get(v___x_2947_, 7);
                v_infoState_2957_ = crate::leanh::lean_ctor_get(v___x_2947_, 8);
                v_snapshotTasks_2958_ = crate::leanh::lean_ctor_get(v___x_2947_, 10);
                v_isSharedCheck_2988_ = (!crate::leanh::lean_is_exclusive(v___x_2947_)) as u8;
                if v_isSharedCheck_2988_ == 0 {
                    v___x_2960_ = v___x_2947_;
                    v_isShared_2961_ = v_isSharedCheck_2988_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2958_);
                    crate::leanh::lean_inc(v_traceState_2948_);
                    crate::leanh::lean_inc(v_infoState_2957_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2956_);
                    crate::leanh::lean_inc(v_ngen_2955_);
                    crate::leanh::lean_inc(v_maxRecDepth_2954_);
                    crate::leanh::lean_inc(v_nextMacroScope_2953_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_2952_);
                    crate::leanh::lean_inc(v_scopes_2951_);
                    crate::leanh::lean_inc(v_messages_2950_);
                    crate::leanh::lean_inc(v_env_2949_);
                    crate::leanh::lean_dec(v___x_2947_);
                    v___x_2960_ = crate::leanh::lean_box(0);
                    v_isShared_2961_ = v_isSharedCheck_2988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2962_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2948_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2963_ = crate::leanh::lean_ctor_get(v_traceState_2948_, 0);
                v_isSharedCheck_2987_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2948_)) as u8;
                if v_isSharedCheck_2987_ == 0 {
                    v___x_2965_ = v_traceState_2948_;
                    v_isShared_2966_ = v_isSharedCheck_2987_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2963_);
                    crate::leanh::lean_dec(v_traceState_2948_);
                    v___x_2965_ = crate::leanh::lean_box(0);
                    v_isShared_2966_ = v_isSharedCheck_2987_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2967_ = crate::leanh::lean_box(0);
                v___x_2968_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__0);
                v___x_2969_ = 0;
                v___x_2970_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1;
                v___x_2971_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2971_, 0, v_cls_2935_);
                crate::leanh::lean_ctor_set(v___x_2971_, 1, v___x_2967_);
                crate::leanh::lean_ctor_set(v___x_2971_, 2, v___x_2970_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2971_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2968_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2971_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2968_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2971_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2969_,
                );
                v___x_2972_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__2;
                v___x_2973_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2973_, 0, v___x_2971_);
                crate::leanh::lean_ctor_set(v___x_2973_, 1, v_a_2943_);
                crate::leanh::lean_ctor_set(v___x_2973_, 2, v___x_2972_);
                v___x_2974_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2974_, 0, v_a_2941_);
                crate::leanh::lean_ctor_set(v___x_2974_, 1, v___x_2973_);
                v___x_2975_ = l_Lean_PersistentArray_push___redArg(v_traces_2963_, v___x_2974_);
                if v_isShared_2966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2965_, 0, v___x_2975_);
                    v___x_2977_ = v___x_2965_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2975_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2986_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2962_,
                    );
                    v___x_2977_ = v_reuseFailAlloc_2986_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2961_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2960_, 9, v___x_2977_);
                    v___x_2979_ = v___x_2960_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2985_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_env_2949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_messages_2950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_scopes_2951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 3, v_usedQuotCtxts_2952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 4, v_nextMacroScope_2953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 5, v_maxRecDepth_2954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 6, v_ngen_2955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 7, v_auxDeclNGen_2956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 8, v_infoState_2957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 9, v___x_2977_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 10, v_snapshotTasks_2958_);
                    v___x_2979_ = v_reuseFailAlloc_2985_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2980_ = lean_st_ref_set(v___y_2938_, v___x_2979_);
                v___x_2981_ = crate::leanh::lean_box(0);
                if v_isShared_2946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2945_, 0, v___x_2981_);
                    v___x_2983_ = v___x_2945_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
                    v___x_2983_ = v_reuseFailAlloc_2984_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2983_;
            }
            7 => {
                if v_isShared_2993_ == 0 {
                    v___x_2995_ = v___x_2992_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2996_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
                    v___x_2995_ = v_reuseFailAlloc_2996_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___boxed(
    mut v_cls_2998_: *mut crate::leanh::LeanObject,
    mut v_msg_2999_: *mut crate::leanh::LeanObject,
    mut v___y_3000_: *mut crate::leanh::LeanObject,
    mut v___y_3001_: *mut crate::leanh::LeanObject,
    mut v___y_3002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3003_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(
        v_cls_2998_,
        v_msg_2999_,
        v___y_3000_,
        v___y_3001_,
    );
    crate::leanh::lean_dec(v___y_3001_);
    crate::leanh::lean_dec_ref(v___y_3000_);
    return v_res_3003_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(
    mut v_keys_3004_: *mut crate::leanh::LeanObject,
    mut v_i_3005_: *mut crate::leanh::LeanObject,
    mut v_k_3006_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v_k_x27_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: u8 = 0;
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3007_ = lean_array_get_size(v_keys_3004_);
                v___x_3008_ = lean_nat_dec_lt(v_i_3005_, v___x_3007_);
                if v___x_3008_ == 0 {
                    crate::leanh::lean_dec(v_i_3005_);
                    return v___x_3008_;
                } else {
                    v_k_x27_3009_ = lean_array_fget_borrowed(v_keys_3004_, v_i_3005_);
                    v___x_3010_ = l_Lean_instBEqExtraModUse_beq(v_k_3006_, v_k_x27_3009_);
                    if v___x_3010_ == 0 {
                        v___x_3011_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3012_ = lean_nat_add(v_i_3005_, v___x_3011_);
                        crate::leanh::lean_dec(v_i_3005_);
                        v_i_3005_ = v___x_3012_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_3005_);
                        return v___x_3010_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg___boxed(
    mut v_keys_3014_: *mut crate::leanh::LeanObject,
    mut v_i_3015_: *mut crate::leanh::LeanObject,
    mut v_k_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3017_: u8 = 0;
    let mut v_r_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3017_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_3014_, v_i_3015_, v_k_3016_);
    crate::leanh::lean_dec_ref(v_k_3016_);
    crate::leanh::lean_dec_ref(v_keys_3014_);
    v_r_3018_ = crate::leanh::lean_box((v_res_3017_) as usize);
    return v_r_3018_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0()
-> usize {
    let mut v___x_3019_: usize = 0;
    let mut v___x_3020_: usize = 0;
    let mut v___x_3021_: usize = 0;
    v___x_3019_ = 5usize;
    v___x_3020_ = 1usize;
    v___x_3021_ = lean_usize_shift_left(v___x_3020_, v___x_3019_);
    return v___x_3021_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1()
-> usize {
    let mut v___x_3022_: usize = 0;
    let mut v___x_3023_: usize = 0;
    let mut v___x_3024_: usize = 0;
    v___x_3022_ = 1usize;
    v___x_3023_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__0);
    v___x_3024_ = lean_usize_sub(v___x_3023_, v___x_3022_);
    return v___x_3024_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(
    mut v_x_3025_: *mut crate::leanh::LeanObject,
    mut v_x_3026_: usize,
    mut v_x_3027_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: usize = 0;
    let mut v___x_3031_: usize = 0;
    let mut v___x_3032_: usize = 0;
    let mut v_j_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: u8 = 0;
    let mut v_node_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: usize = 0;
    let mut v___x_3040_: u8 = 0;
    let mut v_ks_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3025_) == 0 {
                    v_es_3028_ = crate::leanh::lean_ctor_get(v_x_3025_, 0);
                    v___x_3029_ = crate::leanh::lean_box(2);
                    v___x_3030_ = 5usize;
                    v___x_3031_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___closed__1);
                    v___x_3032_ = lean_usize_land(v_x_3026_, v___x_3031_);
                    v_j_3033_ = lean_usize_to_nat(v___x_3032_);
                    v___x_3034_ = lean_array_get_borrowed(v___x_3029_, v_es_3028_, v_j_3033_);
                    crate::leanh::lean_dec(v_j_3033_);
                    match crate::leanh::lean_obj_tag(v___x_3034_) {
                        0 => {
                            v_key_3035_ = crate::leanh::lean_ctor_get(v___x_3034_, 0);
                            v___x_3036_ = l_Lean_instBEqExtraModUse_beq(v_x_3027_, v_key_3035_);
                            return v___x_3036_;
                        }
                        1 => {
                            v_node_3037_ = crate::leanh::lean_ctor_get(v___x_3034_, 0);
                            v___x_3038_ = lean_usize_shift_right(v_x_3026_, v___x_3030_);
                            v_x_3025_ = v_node_3037_;
                            v_x_3026_ = v___x_3038_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3040_ = 0;
                            return v___x_3040_;
                        }
                    }
                } else {
                    v_ks_3041_ = crate::leanh::lean_ctor_get(v_x_3025_, 0);
                    v___x_3042_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3043_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_ks_3041_, v___x_3042_, v_x_3027_);
                    return v___x_3043_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg___boxed(
    mut v_x_3044_: *mut crate::leanh::LeanObject,
    mut v_x_3045_: *mut crate::leanh::LeanObject,
    mut v_x_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_16987__boxed_3047_: usize = 0;
    let mut v_res_3048_: u8 = 0;
    let mut v_r_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_16987__boxed_3047_ = crate::leanh::lean_unbox_usize(v_x_3045_);
    crate::leanh::lean_dec(v_x_3045_);
    v_res_3048_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3044_, v_x_16987__boxed_3047_, v_x_3046_);
    crate::leanh::lean_dec_ref(v_x_3046_);
    crate::leanh::lean_dec_ref(v_x_3044_);
    v_r_3049_ = crate::leanh::lean_box((v_res_3048_) as usize);
    return v_r_3049_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(
    mut v_x_3050_: *mut crate::leanh::LeanObject,
    mut v_x_3051_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3052_: u64 = 0;
    let mut v___x_3053_: usize = 0;
    let mut v___x_3054_: u8 = 0;
    v___x_3052_ = l_Lean_instHashableExtraModUse_hash(v_x_3051_);
    v___x_3053_ = lean_uint64_to_usize(v___x_3052_);
    v___x_3054_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3050_, v___x_3053_, v_x_3051_);
    return v___x_3054_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_x_3055_: *mut crate::leanh::LeanObject,
    mut v_x_3056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3057_: u8 = 0;
    let mut v_r_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3057_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_3055_, v_x_3056_);
    crate::leanh::lean_dec_ref(v_x_3056_);
    crate::leanh::lean_dec_ref(v_x_3055_);
    v_r_3058_ = crate::leanh::lean_box((v_res_3057_) as usize);
    return v_r_3058_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3061_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__1;
    v___x_3062_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__0;
    v___x_3063_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3062_,
        v___x_3061_,
    );
    return v___x_3063_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3068_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__5;
    v___x_3069_ = l_Lean_stringToMessageData(v___x_3068_);
    return v___x_3069_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3071_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__7;
    v___x_3072_ = l_Lean_stringToMessageData(v___x_3071_);
    return v___x_3072_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3073_ =
        l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1___closed__1;
    v___x_3074_ = l_Lean_stringToMessageData(v___x_3073_);
    return v___x_3074_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_3078_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4;
    v___x_3079_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11;
    v___x_3080_ = l_Lean_Name_append(v___x_3079_, v_cls_3078_);
    return v___x_3080_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3082_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__13;
    v___x_3083_ = l_Lean_stringToMessageData(v___x_3082_);
    return v___x_3083_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3085_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__15;
    v___x_3086_ = l_Lean_stringToMessageData(v___x_3085_);
    return v___x_3086_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(
    mut v_mod_3091_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3092_: u8,
    mut v_hint_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3099_: u8 = 0;
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3124_: u8 = 0;
    let mut v_asyncMode_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3133_: u8 = 0;
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3143_: u8 = 0;
    let mut v_cls_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: u8 = 0;
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3097_ = lean_st_ref_get(v___y_3095_);
                v_env_3098_ = crate::leanh::lean_ctor_get(v___x_3097_, 0);
                crate::leanh::lean_inc_ref(v_env_3098_);
                crate::leanh::lean_dec(v___x_3097_);
                v_isExporting_3099_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_3098_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_3098_);
                v___x_3100_ = lean_st_ref_get(v___y_3095_);
                v_env_3101_ = crate::leanh::lean_ctor_get(v___x_3100_, 0);
                crate::leanh::lean_inc_ref(v_env_3101_);
                crate::leanh::lean_dec(v___x_3100_);
                v___x_3102_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__2);
                crate::leanh::lean_inc(v_mod_3091_);
                v_entry_3103_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_3103_, 0, v_mod_3091_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_3103_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_3099_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_3103_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_3092_,
                );
                v___x_3104_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_3105_ = crate::leanh::lean_box(1);
                v___x_3106_ = crate::leanh::lean_box(0);
                v___x_3134_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_3102_,
                    v___x_3104_,
                    v_env_3101_,
                    v___x_3105_,
                    v___x_3106_,
                );
                v___x_3135_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v___x_3134_, v_entry_3103_);
                crate::leanh::lean_dec(v___x_3134_);
                if v___x_3135_ == 0 {
                    v___x_3136_ = l_Lean_inheritedTraceOptions;
                    v___x_3137_ = lean_st_ref_get(v___x_3136_);
                    v___x_3138_ = lean_st_ref_get(v___y_3095_);
                    v_scopes_3139_ = crate::leanh::lean_ctor_get(v___x_3138_, 2);
                    crate::leanh::lean_inc(v_scopes_3139_);
                    crate::leanh::lean_dec(v___x_3138_);
                    v___x_3140_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_3141_ = l_List_head_x21___redArg(v___x_3140_, v_scopes_3139_);
                    crate::leanh::lean_dec(v_scopes_3139_);
                    v_opts_3142_ = crate::leanh::lean_ctor_get(v___x_3141_, 1);
                    crate::leanh::lean_inc_ref(v_opts_3142_);
                    crate::leanh::lean_dec(v___x_3141_);
                    v_hasTrace_3143_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_3142_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3143_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_3142_);
                        crate::leanh::lean_dec(v___x_3137_);
                        crate::leanh::lean_dec(v_hint_3093_);
                        crate::leanh::lean_dec(v_mod_3091_);
                        v___y_3108_ = v___y_3095_;
                        state = 1;
                        continue;
                    } else {
                        v_cls_3144_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__4;
                        v___x_3164_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__12);
                        v___x_3165_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_3137_,
                            v_opts_3142_,
                            v___x_3164_,
                        );
                        crate::leanh::lean_dec_ref(v_opts_3142_);
                        crate::leanh::lean_dec(v___x_3137_);
                        if v___x_3165_ == 0 {
                            crate::leanh::lean_dec(v_hint_3093_);
                            crate::leanh::lean_dec(v_mod_3091_);
                            v___y_3108_ = v___y_3095_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3166_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__14);
                            if v_isExporting_3099_ == 0 {
                                v___x_3175_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__19;
                                v___y_3168_ = v___x_3175_;
                                state = 6;
                                continue;
                            } else {
                                v___x_3176_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__20;
                                v___y_3168_ = v___x_3176_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_3103_, 1);
                    crate::leanh::lean_dec(v_hint_3093_);
                    crate::leanh::lean_dec(v_mod_3091_);
                    v___x_3177_ = crate::leanh::lean_box(0);
                    v___x_3178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3178_, 0, v___x_3177_);
                    return v___x_3178_;
                }
            }
            1 => {
                v___x_3109_ = lean_st_ref_take(v___y_3108_);
                v_toEnvExtension_3110_ = crate::leanh::lean_ctor_get(v___x_3104_, 0);
                v_env_3111_ = crate::leanh::lean_ctor_get(v___x_3109_, 0);
                v_messages_3112_ = crate::leanh::lean_ctor_get(v___x_3109_, 1);
                v_scopes_3113_ = crate::leanh::lean_ctor_get(v___x_3109_, 2);
                v_usedQuotCtxts_3114_ = crate::leanh::lean_ctor_get(v___x_3109_, 3);
                v_nextMacroScope_3115_ = crate::leanh::lean_ctor_get(v___x_3109_, 4);
                v_maxRecDepth_3116_ = crate::leanh::lean_ctor_get(v___x_3109_, 5);
                v_ngen_3117_ = crate::leanh::lean_ctor_get(v___x_3109_, 6);
                v_auxDeclNGen_3118_ = crate::leanh::lean_ctor_get(v___x_3109_, 7);
                v_infoState_3119_ = crate::leanh::lean_ctor_get(v___x_3109_, 8);
                v_traceState_3120_ = crate::leanh::lean_ctor_get(v___x_3109_, 9);
                v_snapshotTasks_3121_ = crate::leanh::lean_ctor_get(v___x_3109_, 10);
                v_isSharedCheck_3133_ = (!crate::leanh::lean_is_exclusive(v___x_3109_)) as u8;
                if v_isSharedCheck_3133_ == 0 {
                    v___x_3123_ = v___x_3109_;
                    v_isShared_3124_ = v_isSharedCheck_3133_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3121_);
                    crate::leanh::lean_inc(v_traceState_3120_);
                    crate::leanh::lean_inc(v_infoState_3119_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3118_);
                    crate::leanh::lean_inc(v_ngen_3117_);
                    crate::leanh::lean_inc(v_maxRecDepth_3116_);
                    crate::leanh::lean_inc(v_nextMacroScope_3115_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_3114_);
                    crate::leanh::lean_inc(v_scopes_3113_);
                    crate::leanh::lean_inc(v_messages_3112_);
                    crate::leanh::lean_inc(v_env_3111_);
                    crate::leanh::lean_dec(v___x_3109_);
                    v___x_3123_ = crate::leanh::lean_box(0);
                    v_isShared_3124_ = v_isSharedCheck_3133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_3125_ = crate::leanh::lean_ctor_get(v_toEnvExtension_3110_, 2);
                v___x_3126_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3104_,
                    v_env_3111_,
                    v_entry_3103_,
                    v_asyncMode_3125_,
                    v___x_3106_,
                );
                if v_isShared_3124_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3123_, 0, v___x_3126_);
                    v___x_3128_ = v___x_3123_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3132_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_messages_3112_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 2, v_scopes_3113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 3, v_usedQuotCtxts_3114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 4, v_nextMacroScope_3115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 5, v_maxRecDepth_3116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 6, v_ngen_3117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 7, v_auxDeclNGen_3118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 8, v_infoState_3119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 9, v_traceState_3120_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 10, v_snapshotTasks_3121_);
                    v___x_3128_ = v_reuseFailAlloc_3132_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3129_ = lean_st_ref_set(v___y_3108_, v___x_3128_);
                v___x_3130_ = crate::leanh::lean_box(0);
                v___x_3131_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3131_, 0, v___x_3130_);
                return v___x_3131_;
            }
            4 => {
                v___x_3148_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3148_, 0, v___y_3146_);
                crate::leanh::lean_ctor_set(v___x_3148_, 1, v___y_3147_);
                v___x_3149_ =
                    l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(
                        v_cls_3144_,
                        v___x_3148_,
                        v___y_3094_,
                        v___y_3095_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3149_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3149_, 1);
                    v___y_3108_ = v___y_3095_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_3103_, 1);
                    return v___x_3149_;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_3152_);
                v___x_3153_ = l_Lean_stringToMessageData(v___y_3152_);
                v___x_3154_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3154_, 0, v___y_3151_);
                crate::leanh::lean_ctor_set(v___x_3154_, 1, v___x_3153_);
                v___x_3155_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__6);
                v___x_3156_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3156_, 0, v___x_3154_);
                crate::leanh::lean_ctor_set(v___x_3156_, 1, v___x_3155_);
                v___x_3157_ = l_Lean_MessageData_ofName(v_mod_3091_);
                v___x_3158_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3158_, 0, v___x_3156_);
                crate::leanh::lean_ctor_set(v___x_3158_, 1, v___x_3157_);
                v___x_3159_ = l_Lean_Name_isAnonymous(v_hint_3093_);
                if v___x_3159_ == 0 {
                    v___x_3160_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__8);
                    v___x_3161_ = l_Lean_MessageData_ofName(v_hint_3093_);
                    v___x_3162_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3162_, 0, v___x_3160_);
                    crate::leanh::lean_ctor_set(v___x_3162_, 1, v___x_3161_);
                    v___y_3146_ = v___x_3158_;
                    v___y_3147_ = v___x_3162_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_3093_);
                    v___x_3163_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__9);
                    v___y_3146_ = v___x_3158_;
                    v___y_3147_ = v___x_3163_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_3168_);
                v___x_3169_ = l_Lean_stringToMessageData(v___y_3168_);
                v___x_3170_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3170_, 0, v___x_3166_);
                crate::leanh::lean_ctor_set(v___x_3170_, 1, v___x_3169_);
                v___x_3171_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__16);
                v___x_3172_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3172_, 0, v___x_3170_);
                crate::leanh::lean_ctor_set(v___x_3172_, 1, v___x_3171_);
                if v_isMeta_3092_ == 0 {
                    v___x_3173_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__17;
                    v___y_3151_ = v___x_3172_;
                    v___y_3152_ = v___x_3173_;
                    state = 5;
                    continue;
                } else {
                    v___x_3174_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__18;
                    v___y_3151_ = v___x_3172_;
                    v___y_3152_ = v___x_3174_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___boxed(
    mut v_mod_3179_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3180_: *mut crate::leanh::LeanObject,
    mut v_hint_3181_: *mut crate::leanh::LeanObject,
    mut v___y_3182_: *mut crate::leanh::LeanObject,
    mut v___y_3183_: *mut crate::leanh::LeanObject,
    mut v___y_3184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_3185_: u8 = 0;
    let mut v_res_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3185_ = (crate::leanh::lean_unbox(v_isMeta_3180_) as u8);
    v_res_3186_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_mod_3179_, v_isMeta_boxed_3185_, v_hint_3181_, v___y_3182_, v___y_3183_);
    crate::leanh::lean_dec(v___y_3183_);
    crate::leanh::lean_dec_ref(v___y_3182_);
    return v_res_3186_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(
    mut v___x_3187_: *mut crate::leanh::LeanObject,
    mut v_declName_3188_: *mut crate::leanh::LeanObject,
    mut v_as_3189_: *mut crate::leanh::LeanObject,
    mut v_sz_3190_: usize,
    mut v_i_3191_: usize,
    mut v_b_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3196_: u8 = 0;
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: u8 = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: usize = 0;
    let mut v___x_3209_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3196_ = lean_usize_dec_lt(v_i_3191_, v_sz_3190_);
                if v___x_3196_ == 0 {
                    crate::leanh::lean_dec(v_declName_3188_);
                    v___x_3197_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3197_, 0, v_b_3192_);
                    return v___x_3197_;
                } else {
                    v___x_3198_ = l_Lean_Environment_header(v___x_3187_);
                    v_modules_3199_ = crate::leanh::lean_ctor_get(v___x_3198_, 3);
                    crate::leanh::lean_inc_ref(v_modules_3199_);
                    crate::leanh::lean_dec_ref(v___x_3198_);
                    v___x_3200_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_3201_ = lean_array_uget_borrowed(v_as_3189_, v_i_3191_);
                    v___x_3202_ = lean_array_get(v___x_3200_, v_modules_3199_, v_a_3201_);
                    crate::leanh::lean_dec_ref(v_modules_3199_);
                    v_toImport_3203_ = crate::leanh::lean_ctor_get(v___x_3202_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_3203_);
                    crate::leanh::lean_dec(v___x_3202_);
                    v_module_3204_ = crate::leanh::lean_ctor_get(v_toImport_3203_, 0);
                    crate::leanh::lean_inc(v_module_3204_);
                    crate::leanh::lean_dec_ref(v_toImport_3203_);
                    v___x_3205_ = 0;
                    crate::leanh::lean_inc(v_declName_3188_);
                    v___x_3206_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_3204_, v___x_3205_, v_declName_3188_, v___y_3193_, v___y_3194_);
                    if crate::leanh::lean_obj_tag(v___x_3206_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3206_, 1);
                        v___x_3207_ = crate::leanh::lean_box(0);
                        v___x_3208_ = 1usize;
                        v___x_3209_ = lean_usize_add(v_i_3191_, v___x_3208_);
                        v_i_3191_ = v___x_3209_;
                        v_b_3192_ = v___x_3207_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_3188_);
                        return v___x_3206_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4___boxed(
    mut v___x_3211_: *mut crate::leanh::LeanObject,
    mut v_declName_3212_: *mut crate::leanh::LeanObject,
    mut v_as_3213_: *mut crate::leanh::LeanObject,
    mut v_sz_3214_: *mut crate::leanh::LeanObject,
    mut v_i_3215_: *mut crate::leanh::LeanObject,
    mut v_b_3216_: *mut crate::leanh::LeanObject,
    mut v___y_3217_: *mut crate::leanh::LeanObject,
    mut v___y_3218_: *mut crate::leanh::LeanObject,
    mut v___y_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3220_: usize = 0;
    let mut v_i_boxed_3221_: usize = 0;
    let mut v_res_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3220_ = crate::leanh::lean_unbox_usize(v_sz_3214_);
    crate::leanh::lean_dec(v_sz_3214_);
    v_i_boxed_3221_ = crate::leanh::lean_unbox_usize(v_i_3215_);
    crate::leanh::lean_dec(v_i_3215_);
    v_res_3222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v___x_3211_, v_declName_3212_, v_as_3213_, v_sz_boxed_3220_, v_i_boxed_3221_, v_b_3216_, v___y_3217_, v___y_3218_);
    crate::leanh::lean_dec(v___y_3218_);
    crate::leanh::lean_dec_ref(v___y_3217_);
    crate::leanh::lean_dec_ref(v_as_3213_);
    crate::leanh::lean_dec_ref(v___x_3211_);
    return v_res_3222_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(
    mut v_a_3223_: *mut crate::leanh::LeanObject,
    mut v_x_3224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3224_) == 0 {
                    v___x_3225_ = crate::leanh::lean_box(0);
                    return v___x_3225_;
                } else {
                    v_key_3226_ = crate::leanh::lean_ctor_get(v_x_3224_, 0);
                    v_value_3227_ = crate::leanh::lean_ctor_get(v_x_3224_, 1);
                    v_tail_3228_ = crate::leanh::lean_ctor_get(v_x_3224_, 2);
                    v___x_3229_ = lean_name_eq(v_key_3226_, v_a_3223_);
                    if v___x_3229_ == 0 {
                        v_x_3224_ = v_tail_3228_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3227_);
                        v___x_3231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3231_, 0, v_value_3227_);
                        return v___x_3231_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg___boxed(
    mut v_a_3232_: *mut crate::leanh::LeanObject,
    mut v_x_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3234_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_3232_, v_x_3233_);
    crate::leanh::lean_dec(v_x_3233_);
    crate::leanh::lean_dec(v_a_3232_);
    return v_res_3234_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u64 = 0;
    v___x_3235_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_3236_ = lean_uint64_of_nat(v___x_3235_);
    return v___x_3236_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(
    mut v_m_3237_: *mut crate::leanh::LeanObject,
    mut v_a_3238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3242_: u64 = 0;
    let mut v___x_3243_: u64 = 0;
    let mut v___x_3244_: u64 = 0;
    let mut v_fold_3245_: u64 = 0;
    let mut v___x_3246_: u64 = 0;
    let mut v___x_3247_: u64 = 0;
    let mut v___x_3248_: u64 = 0;
    let mut v___x_3249_: usize = 0;
    let mut v___x_3250_: usize = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: usize = 0;
    let mut v___x_3253_: usize = 0;
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: u64 = 0;
    let mut v_hash_3257_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3239_ = crate::leanh::lean_ctor_get(v_m_3237_, 1);
                v___x_3240_ = lean_array_get_size(v_buckets_3239_);
                if crate::leanh::lean_obj_tag(v_a_3238_) == 0 {
                    v___x_3256_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___closed__0);
                    v___y_3242_ = v___x_3256_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3257_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_3238_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3242_ = v_hash_3257_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3243_ = 32u64;
                v___x_3244_ = lean_uint64_shift_right(v___y_3242_, v___x_3243_);
                v_fold_3245_ = lean_uint64_xor(v___y_3242_, v___x_3244_);
                v___x_3246_ = 16u64;
                v___x_3247_ = lean_uint64_shift_right(v_fold_3245_, v___x_3246_);
                v___x_3248_ = lean_uint64_xor(v_fold_3245_, v___x_3247_);
                v___x_3249_ = lean_uint64_to_usize(v___x_3248_);
                v___x_3250_ = lean_usize_of_nat(v___x_3240_);
                v___x_3251_ = 1usize;
                v___x_3252_ = lean_usize_sub(v___x_3250_, v___x_3251_);
                v___x_3253_ = lean_usize_land(v___x_3249_, v___x_3252_);
                v___x_3254_ = lean_array_uget_borrowed(v_buckets_3239_, v___x_3253_);
                v___x_3255_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_3238_, v___x_3254_);
                return v___x_3255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_m_3258_: *mut crate::leanh::LeanObject,
    mut v_a_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_3258_, v_a_3259_);
    crate::leanh::lean_dec(v_a_3259_);
    crate::leanh::lean_dec_ref(v_m_3258_);
    return v_res_3260_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3263_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__1;
    v___x_3264_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__0;
    v___x_3265_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3264_,
        v___x_3263_,
    );
    return v___x_3265_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(
    mut v_declName_3268_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3269_: u8,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
    mut v___y_3271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3281_: usize = 0;
    let mut v___x_3282_: usize = 0;
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3286_: u8 = 0;
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v_unused_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: u8 = 0;
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3303_: u8 = 0;
    let mut v_toImport_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3273_ = lean_st_ref_get(v___y_3271_);
                v_env_3277_ = crate::leanh::lean_ctor_get(v___x_3273_, 0);
                crate::leanh::lean_inc_ref(v_env_3277_);
                crate::leanh::lean_dec(v___x_3273_);
                v___x_3292_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3277_, v_declName_3268_);
                if crate::leanh::lean_obj_tag(v___x_3292_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_3277_);
                    crate::leanh::lean_dec(v_declName_3268_);
                    state = 1;
                    continue;
                } else {
                    v_val_3293_ = crate::leanh::lean_ctor_get(v___x_3292_, 0);
                    crate::leanh::lean_inc(v_val_3293_);
                    crate::leanh::lean_dec_ref_known(v___x_3292_, 1);
                    v___x_3294_ = l_Lean_Environment_header(v_env_3277_);
                    v_modules_3295_ = crate::leanh::lean_ctor_get(v___x_3294_, 3);
                    crate::leanh::lean_inc_ref(v_modules_3295_);
                    crate::leanh::lean_dec_ref(v___x_3294_);
                    v___x_3296_ = lean_array_get_size(v_modules_3295_);
                    v___x_3297_ = lean_nat_dec_lt(v_val_3293_, v___x_3296_);
                    if v___x_3297_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_3295_);
                        crate::leanh::lean_dec(v_val_3293_);
                        crate::leanh::lean_dec_ref(v_env_3277_);
                        crate::leanh::lean_dec(v_declName_3268_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3298_ = lean_st_ref_get(v___y_3271_);
                        v_env_3299_ = crate::leanh::lean_ctor_get(v___x_3298_, 0);
                        crate::leanh::lean_inc_ref(v_env_3299_);
                        crate::leanh::lean_dec(v___x_3298_);
                        v___x_3300_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__2);
                        v___x_3301_ = lean_array_fget(v_modules_3295_, v_val_3293_);
                        crate::leanh::lean_dec(v_val_3293_);
                        crate::leanh::lean_dec_ref(v_modules_3295_);
                        if v_isMeta_3269_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_3299_);
                            v___y_3303_ = v_isMeta_3269_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_3268_);
                            v___x_3314_ = l_Lean_isMarkedMeta(v_env_3299_, v_declName_3268_);
                            if v___x_3314_ == 0 {
                                v___y_3303_ = v_isMeta_3269_;
                                state = 5;
                                continue;
                            } else {
                                v___x_3315_ = 0;
                                v___y_3303_ = v___x_3315_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3275_ = crate::leanh::lean_box(0);
                v___x_3276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3276_, 0, v___x_3275_);
                return v___x_3276_;
            }
            2 => {
                v___x_3280_ = crate::leanh::lean_box(0);
                v_sz_3281_ = lean_array_size(v___y_3279_);
                v___x_3282_ = 0usize;
                v___x_3283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__4(v_env_3277_, v_declName_3268_, v___y_3279_, v_sz_3281_, v___x_3282_, v___x_3280_, v___y_3270_, v___y_3271_);
                crate::leanh::lean_dec_ref(v___y_3279_);
                crate::leanh::lean_dec_ref(v_env_3277_);
                if crate::leanh::lean_obj_tag(v___x_3283_) == 0 {
                    v_isSharedCheck_3290_ = (!crate::leanh::lean_is_exclusive(v___x_3283_)) as u8;
                    if v_isSharedCheck_3290_ == 0 {
                        v_unused_3291_ = crate::leanh::lean_ctor_get(v___x_3283_, 0);
                        crate::leanh::lean_dec(v_unused_3291_);
                        v___x_3285_ = v___x_3283_;
                        v_isShared_3286_ = v_isSharedCheck_3290_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3283_);
                        v___x_3285_ = crate::leanh::lean_box(0);
                        v_isShared_3286_ = v_isSharedCheck_3290_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_3283_;
                }
            }
            3 => {
                if v_isShared_3286_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3285_, 0, v___x_3280_);
                    v___x_3288_ = v___x_3285_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3280_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3288_;
            }
            5 => {
                v_toImport_3304_ = crate::leanh::lean_ctor_get(v___x_3301_, 0);
                crate::leanh::lean_inc_ref(v_toImport_3304_);
                crate::leanh::lean_dec(v___x_3301_);
                v_module_3305_ = crate::leanh::lean_ctor_get(v_toImport_3304_, 0);
                crate::leanh::lean_inc(v_module_3305_);
                crate::leanh::lean_dec_ref(v_toImport_3304_);
                crate::leanh::lean_inc(v_declName_3268_);
                v___x_3306_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3(v_module_3305_, v___y_3303_, v_declName_3268_, v___y_3270_, v___y_3271_);
                if crate::leanh::lean_obj_tag(v___x_3306_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3306_, 1);
                    v___x_3307_ = l_Lean_indirectModUseExt;
                    v___x_3308_ = crate::leanh::lean_box(1);
                    v___x_3309_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_3277_);
                    v___x_3310_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_3300_,
                        v___x_3307_,
                        v_env_3277_,
                        v___x_3308_,
                        v___x_3309_,
                    );
                    v___x_3311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v___x_3310_, v_declName_3268_);
                    crate::leanh::lean_dec(v___x_3310_);
                    if crate::leanh::lean_obj_tag(v___x_3311_) == 0 {
                        v___x_3312_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___closed__3;
                        v___y_3279_ = v___x_3312_;
                        state = 2;
                        continue;
                    } else {
                        v_val_3313_ = crate::leanh::lean_ctor_get(v___x_3311_, 0);
                        crate::leanh::lean_inc(v_val_3313_);
                        crate::leanh::lean_dec_ref_known(v___x_3311_, 1);
                        v___y_3279_ = v_val_3313_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3277_);
                    crate::leanh::lean_dec(v_declName_3268_);
                    return v___x_3306_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1___boxed(
    mut v_declName_3316_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3317_: *mut crate::leanh::LeanObject,
    mut v___y_3318_: *mut crate::leanh::LeanObject,
    mut v___y_3319_: *mut crate::leanh::LeanObject,
    mut v___y_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_3321_: u8 = 0;
    let mut v_res_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3321_ = (crate::leanh::lean_unbox(v_isMeta_3317_) as u8);
    v_res_3322_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_declName_3316_, v_isMeta_boxed_3321_, v___y_3318_, v___y_3319_);
    crate::leanh::lean_dec(v___y_3319_);
    crate::leanh::lean_dec_ref(v___y_3318_);
    return v_res_3322_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(
    mut v_as_x27_3323_: *mut crate::leanh::LeanObject,
    mut v_b_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: u8 = 0;
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3323_) == 0 {
                    v___x_3328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3328_, 0, v_b_3324_);
                    return v___x_3328_;
                } else {
                    v_head_3329_ = crate::leanh::lean_ctor_get(v_as_x27_3323_, 0);
                    v_tail_3330_ = crate::leanh::lean_ctor_get(v_as_x27_3323_, 1);
                    v___x_3331_ = 1;
                    crate::leanh::lean_inc(v_head_3329_);
                    v___x_3332_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1(v_head_3329_, v___x_3331_, v___y_3325_, v___y_3326_);
                    if crate::leanh::lean_obj_tag(v___x_3332_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3332_, 1);
                        v___x_3333_ = crate::leanh::lean_box(0);
                        v_as_x27_3323_ = v_tail_3330_;
                        v_b_3324_ = v___x_3333_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3332_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg___boxed(
    mut v_as_x27_3335_: *mut crate::leanh::LeanObject,
    mut v_b_3336_: *mut crate::leanh::LeanObject,
    mut v___y_3337_: *mut crate::leanh::LeanObject,
    mut v___y_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3340_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_3335_, v_b_3336_, v___y_3337_, v___y_3338_);
    crate::leanh::lean_dec(v___y_3338_);
    crate::leanh::lean_dec_ref(v___y_3337_);
    crate::leanh::lean_dec(v_as_x27_3335_);
    return v_res_3340_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(
    mut v_opts_3341_: *mut crate::leanh::LeanObject,
    mut v_opt_3342_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3343_ = crate::leanh::lean_ctor_get(v_opt_3342_, 0);
    v_defValue_3344_ = crate::leanh::lean_ctor_get(v_opt_3342_, 1);
    v_map_3345_ = crate::leanh::lean_ctor_get(v_opts_3341_, 0);
    v___x_3346_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3345_,
            v_name_3343_,
        );
    if crate::leanh::lean_obj_tag(v___x_3346_) == 0 {
        let mut v___x_3347_: u8 = 0;
        v___x_3347_ = (crate::leanh::lean_unbox(v_defValue_3344_) as u8);
        return v___x_3347_;
    } else {
        let mut v_val_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3348_ = crate::leanh::lean_ctor_get(v___x_3346_, 0);
        crate::leanh::lean_inc(v_val_3348_);
        crate::leanh::lean_dec_ref_known(v___x_3346_, 1);
        if crate::leanh::lean_obj_tag(v_val_3348_) == 1 {
            let mut v_v_3349_: u8 = 0;
            v_v_3349_ = crate::leanh::lean_ctor_get_uint8(v_val_3348_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3348_, 0);
            return v_v_3349_;
        } else {
            let mut v___x_3350_: u8 = 0;
            crate::leanh::lean_dec(v_val_3348_);
            v___x_3350_ = (crate::leanh::lean_unbox(v_defValue_3344_) as u8);
            return v___x_3350_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18___boxed(
    mut v_opts_3351_: *mut crate::leanh::LeanObject,
    mut v_opt_3352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3353_: u8 = 0;
    let mut v_r_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(v_opts_3351_, v_opt_3352_);
    crate::leanh::lean_dec_ref(v_opt_3352_);
    crate::leanh::lean_dec_ref(v_opts_3351_);
    v_r_3354_ = crate::leanh::lean_box((v_res_3353_) as usize);
    return v_r_3354_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3355_ = crate::leanh::lean_box(1);
    v___x_3356_ = l_Lean_MessageData_ofFormat(v___x_3355_);
    return v___x_3356_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3360_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__2;
    v___x_3361_ = l_Lean_MessageData_ofFormat(v___x_3360_);
    return v___x_3361_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(
    mut v_x_3362_: *mut crate::leanh::LeanObject,
    mut v_x_3363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v_before_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3385_: u8 = 0;
    let mut v_unused_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3363_) == 0 {
                    return v_x_3362_;
                } else {
                    v_head_3364_ = crate::leanh::lean_ctor_get(v_x_3363_, 0);
                    v_tail_3365_ = crate::leanh::lean_ctor_get(v_x_3363_, 1);
                    v_isSharedCheck_3387_ = (!crate::leanh::lean_is_exclusive(v_x_3363_)) as u8;
                    if v_isSharedCheck_3387_ == 0 {
                        v___x_3367_ = v_x_3363_;
                        v_isShared_3368_ = v_isSharedCheck_3387_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3365_);
                        crate::leanh::lean_inc(v_head_3364_);
                        crate::leanh::lean_dec(v_x_3363_);
                        v___x_3367_ = crate::leanh::lean_box(0);
                        v_isShared_3368_ = v_isSharedCheck_3387_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3369_ = crate::leanh::lean_ctor_get(v_head_3364_, 0);
                v_isSharedCheck_3385_ = (!crate::leanh::lean_is_exclusive(v_head_3364_)) as u8;
                if v_isSharedCheck_3385_ == 0 {
                    v_unused_3386_ = crate::leanh::lean_ctor_get(v_head_3364_, 1);
                    crate::leanh::lean_dec(v_unused_3386_);
                    v___x_3371_ = v_head_3364_;
                    v_isShared_3372_ = v_isSharedCheck_3385_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_3369_);
                    crate::leanh::lean_dec(v_head_3364_);
                    v___x_3371_ = crate::leanh::lean_box(0);
                    v_isShared_3372_ = v_isSharedCheck_3385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3373_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0);
                if v_isShared_3372_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3371_, 7);
                    crate::leanh::lean_ctor_set(v___x_3371_, 1, v___x_3373_);
                    crate::leanh::lean_ctor_set(v___x_3371_, 0, v_x_3362_);
                    v___x_3375_ = v___x_3371_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3384_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_x_3362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3384_, 1, v___x_3373_);
                    v___x_3375_ = v_reuseFailAlloc_3384_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3376_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__3);
                if v_isShared_3368_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3367_, 7);
                    crate::leanh::lean_ctor_set(v___x_3367_, 1, v___x_3376_);
                    crate::leanh::lean_ctor_set(v___x_3367_, 0, v___x_3375_);
                    v___x_3378_ = v___x_3367_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 1, v___x_3376_);
                    v___x_3378_ = v_reuseFailAlloc_3383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3379_ = l_Lean_MessageData_ofSyntax(v_before_3369_);
                v___x_3380_ = l_Lean_indentD(v___x_3379_);
                v___x_3381_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3381_, 0, v___x_3378_);
                crate::leanh::lean_ctor_set(v___x_3381_, 1, v___x_3380_);
                v_x_3362_ = v___x_3381_;
                v_x_3363_ = v_tail_3365_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3391_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__1;
    v___x_3392_ = l_Lean_MessageData_ofFormat(v___x_3391_);
    return v___x_3392_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(
    mut v_msgData_3393_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: u8 = 0;
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3422_: u8 = 0;
    let mut v_unused_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3397_ = lean_st_ref_get(v___y_3395_);
                v_scopes_3398_ = crate::leanh::lean_ctor_get(v___x_3397_, 2);
                crate::leanh::lean_inc(v_scopes_3398_);
                crate::leanh::lean_dec(v___x_3397_);
                v___x_3399_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_3400_ = l_List_head_x21___redArg(v___x_3399_, v_scopes_3398_);
                crate::leanh::lean_dec(v_scopes_3398_);
                v_opts_3401_ = crate::leanh::lean_ctor_get(v___x_3400_, 1);
                crate::leanh::lean_inc_ref(v_opts_3401_);
                crate::leanh::lean_dec(v___x_3400_);
                v___x_3402_ = l_Lean_Elab_pp_macroStack;
                v___x_3403_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__18(v_opts_3401_, v___x_3402_);
                crate::leanh::lean_dec_ref(v_opts_3401_);
                if v___x_3403_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_3394_);
                    v___x_3404_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3404_, 0, v_msgData_3393_);
                    return v___x_3404_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_3394_) == 0 {
                        v___x_3405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3405_, 0, v_msgData_3393_);
                        return v___x_3405_;
                    } else {
                        v_head_3406_ = crate::leanh::lean_ctor_get(v_macroStack_3394_, 0);
                        crate::leanh::lean_inc(v_head_3406_);
                        v_after_3407_ = crate::leanh::lean_ctor_get(v_head_3406_, 1);
                        v_isSharedCheck_3422_ =
                            (!crate::leanh::lean_is_exclusive(v_head_3406_)) as u8;
                        if v_isSharedCheck_3422_ == 0 {
                            v_unused_3423_ = crate::leanh::lean_ctor_get(v_head_3406_, 0);
                            crate::leanh::lean_dec(v_unused_3423_);
                            v___x_3409_ = v_head_3406_;
                            v_isShared_3410_ = v_isSharedCheck_3422_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_3407_);
                            crate::leanh::lean_dec(v_head_3406_);
                            v___x_3409_ = crate::leanh::lean_box(0);
                            v_isShared_3410_ = v_isSharedCheck_3422_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3411_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19___closed__0);
                if v_isShared_3410_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3409_, 7);
                    crate::leanh::lean_ctor_set(v___x_3409_, 1, v___x_3411_);
                    crate::leanh::lean_ctor_set(v___x_3409_, 0, v_msgData_3393_);
                    v___x_3413_ = v___x_3409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3421_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_msgData_3393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 1, v___x_3411_);
                    v___x_3413_ = v_reuseFailAlloc_3421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3414_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___closed__2);
                v___x_3415_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3415_, 0, v___x_3413_);
                crate::leanh::lean_ctor_set(v___x_3415_, 1, v___x_3414_);
                v___x_3416_ = l_Lean_MessageData_ofSyntax(v_after_3407_);
                v___x_3417_ = l_Lean_indentD(v___x_3416_);
                v_msgData_3418_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_3418_, 0, v___x_3415_);
                crate::leanh::lean_ctor_set(v_msgData_3418_, 1, v___x_3417_);
                v___x_3419_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16_spec__19(v_msgData_3418_, v_macroStack_3394_);
                v___x_3420_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3420_, 0, v___x_3419_);
                return v___x_3420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg___boxed(
    mut v_msgData_3424_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3425_: *mut crate::leanh::LeanObject,
    mut v___y_3426_: *mut crate::leanh::LeanObject,
    mut v___y_3427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3428_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_3424_, v_macroStack_3425_, v___y_3426_);
    crate::leanh::lean_dec(v___y_3426_);
    return v_res_3428_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(
    mut v_msg_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3448_: u8 = 0;
    let mut v_a_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3452_: u8 = 0;
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3456_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3433_ = l_Lean_Elab_Command_getRef___redArg(v___y_3430_);
                if crate::leanh::lean_obj_tag(v___x_3433_) == 0 {
                    v_a_3434_ = crate::leanh::lean_ctor_get(v___x_3433_, 0);
                    crate::leanh::lean_inc(v_a_3434_);
                    crate::leanh::lean_dec_ref_known(v___x_3433_, 1);
                    v_macroStack_3435_ = crate::leanh::lean_ctor_get(v___y_3430_, 4);
                    v___x_3436_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msg_3429_, v___y_3431_);
                    v_a_3437_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                    crate::leanh::lean_inc(v_a_3437_);
                    crate::leanh::lean_dec_ref(v___x_3436_);
                    v___x_3438_ = l_Lean_Elab_getBetterRef(v_a_3434_, v_macroStack_3435_);
                    crate::leanh::lean_dec(v_a_3434_);
                    crate::leanh::lean_inc(v_macroStack_3435_);
                    v___x_3439_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_a_3437_, v_macroStack_3435_, v___y_3431_);
                    v_a_3440_ = crate::leanh::lean_ctor_get(v___x_3439_, 0);
                    v_isSharedCheck_3448_ = (!crate::leanh::lean_is_exclusive(v___x_3439_)) as u8;
                    if v_isSharedCheck_3448_ == 0 {
                        v___x_3442_ = v___x_3439_;
                        v_isShared_3443_ = v_isSharedCheck_3448_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3440_);
                        crate::leanh::lean_dec(v___x_3439_);
                        v___x_3442_ = crate::leanh::lean_box(0);
                        v_isShared_3443_ = v_isSharedCheck_3448_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_3429_);
                    v_a_3449_ = crate::leanh::lean_ctor_get(v___x_3433_, 0);
                    v_isSharedCheck_3456_ = (!crate::leanh::lean_is_exclusive(v___x_3433_)) as u8;
                    if v_isSharedCheck_3456_ == 0 {
                        v___x_3451_ = v___x_3433_;
                        v_isShared_3452_ = v_isSharedCheck_3456_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3449_);
                        crate::leanh::lean_dec(v___x_3433_);
                        v___x_3451_ = crate::leanh::lean_box(0);
                        v_isShared_3452_ = v_isSharedCheck_3456_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3444_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3444_, 0, v___x_3438_);
                crate::leanh::lean_ctor_set(v___x_3444_, 1, v_a_3440_);
                if v_isShared_3443_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3442_, 1);
                    crate::leanh::lean_ctor_set(v___x_3442_, 0, v___x_3444_);
                    v___x_3446_ = v___x_3442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3447_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
                    v___x_3446_ = v_reuseFailAlloc_3447_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3446_;
            }
            3 => {
                if v_isShared_3452_ == 0 {
                    v___x_3454_ = v___x_3451_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3455_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
                    v___x_3454_ = v_reuseFailAlloc_3455_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg___boxed(
    mut v_msg_3457_: *mut crate::leanh::LeanObject,
    mut v___y_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3461_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_3457_, v___y_3458_, v___y_3459_);
    crate::leanh::lean_dec(v___y_3459_);
    crate::leanh::lean_dec_ref(v___y_3458_);
    return v_res_3461_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(
    mut v_ref_3462_: *mut crate::leanh::LeanObject,
    mut v_msg_3463_: *mut crate::leanh::LeanObject,
    mut v___y_3464_: *mut crate::leanh::LeanObject,
    mut v___y_3465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3478_: u8 = 0;
    let mut v_ref_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3485_: u8 = 0;
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3467_ = l_Lean_Elab_Command_getRef___redArg(v___y_3464_);
                if crate::leanh::lean_obj_tag(v___x_3467_) == 0 {
                    v_a_3468_ = crate::leanh::lean_ctor_get(v___x_3467_, 0);
                    crate::leanh::lean_inc(v_a_3468_);
                    crate::leanh::lean_dec_ref_known(v___x_3467_, 1);
                    v_fileName_3469_ = crate::leanh::lean_ctor_get(v___y_3464_, 0);
                    v_fileMap_3470_ = crate::leanh::lean_ctor_get(v___y_3464_, 1);
                    v_currRecDepth_3471_ = crate::leanh::lean_ctor_get(v___y_3464_, 2);
                    v_cmdPos_3472_ = crate::leanh::lean_ctor_get(v___y_3464_, 3);
                    v_macroStack_3473_ = crate::leanh::lean_ctor_get(v___y_3464_, 4);
                    v_quotContext_x3f_3474_ = crate::leanh::lean_ctor_get(v___y_3464_, 5);
                    v_currMacroScope_3475_ = crate::leanh::lean_ctor_get(v___y_3464_, 6);
                    v_snap_x3f_3476_ = crate::leanh::lean_ctor_get(v___y_3464_, 8);
                    v_cancelTk_x3f_3477_ = crate::leanh::lean_ctor_get(v___y_3464_, 9);
                    v_suppressElabErrors_3478_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3464_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_3479_ = l_Lean_replaceRef(v_ref_3462_, v_a_3468_);
                    crate::leanh::lean_dec(v_a_3468_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_3477_);
                    crate::leanh::lean_inc(v_snap_x3f_3476_);
                    crate::leanh::lean_inc(v_currMacroScope_3475_);
                    crate::leanh::lean_inc(v_quotContext_x3f_3474_);
                    crate::leanh::lean_inc(v_macroStack_3473_);
                    crate::leanh::lean_inc(v_cmdPos_3472_);
                    crate::leanh::lean_inc(v_currRecDepth_3471_);
                    crate::leanh::lean_inc_ref(v_fileMap_3470_);
                    crate::leanh::lean_inc_ref(v_fileName_3469_);
                    v___x_3480_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3480_, 0, v_fileName_3469_);
                    crate::leanh::lean_ctor_set(v___x_3480_, 1, v_fileMap_3470_);
                    crate::leanh::lean_ctor_set(v___x_3480_, 2, v_currRecDepth_3471_);
                    crate::leanh::lean_ctor_set(v___x_3480_, 3, v_cmdPos_3472_);
                    crate::leanh::lean_ctor_set(v___x_3480_, 4, v_macroStack_3473_);
                    crate::leanh::lean_ctor_set(v___x_3480_, 5, v_quotContext_x3f_3474_);
                    crate::leanh::lean_ctor_set(v___x_3480_, 6, v_currMacroScope_3475_);
                    crate::leanh::lean_ctor_set(v___x_3480_, 7, v_ref_3479_);
                    crate::leanh::lean_ctor_set(v___x_3480_, 8, v_snap_x3f_3476_);
                    crate::leanh::lean_ctor_set(v___x_3480_, 9, v_cancelTk_x3f_3477_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3480_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_3478_,
                    );
                    v___x_3481_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_3463_, v___x_3480_, v___y_3465_);
                    crate::leanh::lean_dec_ref_known(v___x_3480_, 10);
                    return v___x_3481_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_3463_);
                    v_a_3482_ = crate::leanh::lean_ctor_get(v___x_3467_, 0);
                    v_isSharedCheck_3489_ = (!crate::leanh::lean_is_exclusive(v___x_3467_)) as u8;
                    if v_isSharedCheck_3489_ == 0 {
                        v___x_3484_ = v___x_3467_;
                        v_isShared_3485_ = v_isSharedCheck_3489_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3482_);
                        crate::leanh::lean_dec(v___x_3467_);
                        v___x_3484_ = crate::leanh::lean_box(0);
                        v_isShared_3485_ = v_isSharedCheck_3489_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3485_ == 0 {
                    v___x_3487_ = v___x_3484_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
                    v___x_3487_ = v_reuseFailAlloc_3488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg___boxed(
    mut v_ref_3490_: *mut crate::leanh::LeanObject,
    mut v_msg_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3495_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_3490_, v_msg_3491_, v___y_3492_, v___y_3493_);
    crate::leanh::lean_dec(v___y_3493_);
    crate::leanh::lean_dec_ref(v___y_3492_);
    crate::leanh::lean_dec(v_ref_3490_);
    return v_res_3495_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(
    mut v_env_3496_: *mut crate::leanh::LeanObject,
    mut v_declName_3497_: *mut crate::leanh::LeanObject,
    mut v___y_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3500_: u8 = 0;
    let mut v_env_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: u8 = 0;
    v___x_3500_ = 0;
    v_env_3501_ = l_Lean_Environment_setExporting(v_env_3496_, v___x_3500_);
    crate::leanh::lean_inc(v_declName_3497_);
    v___x_3502_ = l_Lean_mkPrivateName(v_env_3501_, v_declName_3497_);
    v___x_3503_ = 1;
    crate::leanh::lean_inc_ref(v_env_3501_);
    v___x_3504_ = l_Lean_Environment_contains(v_env_3501_, v___x_3502_, v___x_3503_);
    if v___x_3504_ == 0 {
        let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3506_: u8 = 0;
        let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3505_ = l_Lean_privateToUserName(v_declName_3497_);
        v___x_3506_ = l_Lean_Environment_contains(v_env_3501_, v___x_3505_, v___x_3503_);
        v___x_3507_ = crate::leanh::lean_box((v___x_3506_) as usize);
        v___x_3508_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3508_, 0, v___x_3507_);
        crate::leanh::lean_ctor_set(v___x_3508_, 1, v___y_3499_);
        return v___x_3508_;
    } else {
        let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_3501_);
        crate::leanh::lean_dec(v_declName_3497_);
        v___x_3509_ = crate::leanh::lean_box((v___x_3504_) as usize);
        v___x_3510_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3510_, 0, v___x_3509_);
        crate::leanh::lean_ctor_set(v___x_3510_, 1, v___y_3499_);
        return v___x_3510_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed(
    mut v_env_3511_: *mut crate::leanh::LeanObject,
    mut v_declName_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
    mut v___y_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3515_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0(v_env_3511_, v_declName_3512_, v___y_3513_, v___y_3514_);
    crate::leanh::lean_dec_ref(v___y_3513_);
    return v_res_3515_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(
    mut v_as_3516_: *mut crate::leanh::LeanObject,
    mut v___y_3517_: *mut crate::leanh::LeanObject,
    mut v___y_3518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3533_: u8 = 0;
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_3516_) == 0 {
                    v___x_3520_ = crate::leanh::lean_box(0);
                    v___x_3521_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3521_, 0, v___x_3520_);
                    return v___x_3521_;
                } else {
                    v_head_3522_ = crate::leanh::lean_ctor_get(v_as_3516_, 0);
                    crate::leanh::lean_inc(v_head_3522_);
                    v_tail_3523_ = crate::leanh::lean_ctor_get(v_as_3516_, 1);
                    crate::leanh::lean_inc(v_tail_3523_);
                    crate::leanh::lean_dec_ref_known(v_as_3516_, 2);
                    v_fst_3524_ = crate::leanh::lean_ctor_get(v_head_3522_, 0);
                    crate::leanh::lean_inc(v_fst_3524_);
                    v_snd_3525_ = crate::leanh::lean_ctor_get(v_head_3522_, 1);
                    crate::leanh::lean_inc(v_snd_3525_);
                    crate::leanh::lean_dec(v_head_3522_);
                    v___x_3526_ = l_Lean_inheritedTraceOptions;
                    v___x_3527_ = lean_st_ref_get(v___x_3526_);
                    v___x_3528_ = lean_st_ref_get(v___y_3518_);
                    v_scopes_3529_ = crate::leanh::lean_ctor_get(v___x_3528_, 2);
                    crate::leanh::lean_inc(v_scopes_3529_);
                    crate::leanh::lean_dec(v___x_3528_);
                    v___x_3530_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_3531_ = l_List_head_x21___redArg(v___x_3530_, v_scopes_3529_);
                    crate::leanh::lean_dec(v_scopes_3529_);
                    v_opts_3532_ = crate::leanh::lean_ctor_get(v___x_3531_, 1);
                    crate::leanh::lean_inc_ref(v_opts_3532_);
                    crate::leanh::lean_dec(v___x_3531_);
                    v_hasTrace_3533_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_3532_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3533_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_3532_);
                        crate::leanh::lean_dec(v___x_3527_);
                        crate::leanh::lean_dec(v_snd_3525_);
                        crate::leanh::lean_dec(v_fst_3524_);
                        v_as_3516_ = v_tail_3523_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3535_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11;
                        crate::leanh::lean_inc(v_fst_3524_);
                        v___x_3536_ = l_Lean_Name_append(v___x_3535_, v_fst_3524_);
                        v___x_3537_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_3527_,
                            v_opts_3532_,
                            v___x_3536_,
                        );
                        crate::leanh::lean_dec(v___x_3536_);
                        crate::leanh::lean_dec_ref(v_opts_3532_);
                        crate::leanh::lean_dec(v___x_3527_);
                        if v___x_3537_ == 0 {
                            crate::leanh::lean_dec(v_snd_3525_);
                            crate::leanh::lean_dec(v_fst_3524_);
                            v_as_3516_ = v_tail_3523_;
                            state = 0;
                            continue;
                        } else {
                            v___x_3539_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3539_, 0, v_snd_3525_);
                            v___x_3540_ = l_Lean_MessageData_ofFormat(v___x_3539_);
                            v___x_3541_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v_fst_3524_, v___x_3540_, v___y_3517_, v___y_3518_);
                            if crate::leanh::lean_obj_tag(v___x_3541_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3541_, 1);
                                v_as_3516_ = v_tail_3523_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_3523_);
                                return v___x_3541_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3___boxed(
    mut v_as_3543_: *mut crate::leanh::LeanObject,
    mut v___y_3544_: *mut crate::leanh::LeanObject,
    mut v___y_3545_: *mut crate::leanh::LeanObject,
    mut v___y_3546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3547_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v_as_3543_, v___y_3544_, v___y_3545_);
    crate::leanh::lean_dec(v___y_3545_);
    crate::leanh::lean_dec_ref(v___y_3544_);
    return v_res_3547_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(
    mut v_env_3548_: *mut crate::leanh::LeanObject,
    mut v_opts_3549_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_3550_: *mut crate::leanh::LeanObject,
    mut v_openDecls_3551_: *mut crate::leanh::LeanObject,
    mut v_n_3552_: *mut crate::leanh::LeanObject,
    mut v___y_3553_: *mut crate::leanh::LeanObject,
    mut v___y_3554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3555_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_3548_,
        v_opts_3549_,
        v_currNamespace_3550_,
        v_openDecls_3551_,
        v_n_3552_,
    );
    v___x_3556_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3556_, 0, v___x_3555_);
    crate::leanh::lean_ctor_set(v___x_3556_, 1, v___y_3554_);
    return v___x_3556_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed(
    mut v_env_3557_: *mut crate::leanh::LeanObject,
    mut v_opts_3558_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_3559_: *mut crate::leanh::LeanObject,
    mut v_openDecls_3560_: *mut crate::leanh::LeanObject,
    mut v_n_3561_: *mut crate::leanh::LeanObject,
    mut v___y_3562_: *mut crate::leanh::LeanObject,
    mut v___y_3563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3564_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4(v_env_3557_, v_opts_3558_, v_currNamespace_3559_, v_openDecls_3560_, v_n_3561_, v___y_3562_, v___y_3563_);
    crate::leanh::lean_dec_ref(v___y_3562_);
    crate::leanh::lean_dec_ref(v_opts_3558_);
    return v_res_3564_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(
    mut v_x_3566_: *mut crate::leanh::LeanObject,
    mut v___y_3567_: *mut crate::leanh::LeanObject,
    mut v___y_3568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3625_: u8 = 0;
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3633_: u8 = 0;
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3637_: u8 = 0;
    let mut v_unused_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3642_: u8 = 0;
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_reuseFailAlloc_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v_unused_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3657_: u8 = 0;
    let mut v_a_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: u8 = 0;
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3674_: u8 = 0;
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3678_: u8 = 0;
    let mut v_a_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3682_: u8 = 0;
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_a_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v_a_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3570_ = lean_st_ref_get(v___y_3568_);
                v_env_3571_ = crate::leanh::lean_ctor_get(v___x_3570_, 0);
                crate::leanh::lean_inc_ref(v_env_3571_);
                crate::leanh::lean_dec(v___x_3570_);
                v___x_3572_ = lean_st_ref_get(v___y_3568_);
                v_scopes_3573_ = crate::leanh::lean_ctor_get(v___x_3572_, 2);
                crate::leanh::lean_inc(v_scopes_3573_);
                crate::leanh::lean_dec(v___x_3572_);
                v___x_3574_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_3575_ = l_List_head_x21___redArg(v___x_3574_, v_scopes_3573_);
                crate::leanh::lean_dec(v_scopes_3573_);
                v_opts_3576_ = crate::leanh::lean_ctor_get(v___x_3575_, 1);
                crate::leanh::lean_inc_ref(v_opts_3576_);
                crate::leanh::lean_dec(v___x_3575_);
                v___x_3577_ = l_Lean_Elab_Command_getScope___redArg(v___y_3568_);
                if crate::leanh::lean_obj_tag(v___x_3577_) == 0 {
                    v_a_3578_ = crate::leanh::lean_ctor_get(v___x_3577_, 0);
                    crate::leanh::lean_inc(v_a_3578_);
                    crate::leanh::lean_dec_ref_known(v___x_3577_, 1);
                    v_currNamespace_3579_ = crate::leanh::lean_ctor_get(v_a_3578_, 2);
                    crate::leanh::lean_inc(v_currNamespace_3579_);
                    crate::leanh::lean_dec(v_a_3578_);
                    v___x_3580_ = l_Lean_Elab_Command_getScope___redArg(v___y_3568_);
                    if crate::leanh::lean_obj_tag(v___x_3580_) == 0 {
                        v_a_3581_ = crate::leanh::lean_ctor_get(v___x_3580_, 0);
                        crate::leanh::lean_inc(v_a_3581_);
                        crate::leanh::lean_dec_ref_known(v___x_3580_, 1);
                        v_openDecls_3582_ = crate::leanh::lean_ctor_get(v_a_3581_, 3);
                        crate::leanh::lean_inc(v_openDecls_3582_);
                        crate::leanh::lean_dec(v_a_3581_);
                        v___x_3583_ = l_Lean_Elab_Command_getRef___redArg(v___y_3567_);
                        if crate::leanh::lean_obj_tag(v___x_3583_) == 0 {
                            v_a_3584_ = crate::leanh::lean_ctor_get(v___x_3583_, 0);
                            crate::leanh::lean_inc(v_a_3584_);
                            crate::leanh::lean_dec_ref_known(v___x_3583_, 1);
                            v___x_3585_ =
                                l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3567_);
                            if crate::leanh::lean_obj_tag(v___x_3585_) == 0 {
                                v_a_3586_ = crate::leanh::lean_ctor_get(v___x_3585_, 0);
                                crate::leanh::lean_inc(v_a_3586_);
                                crate::leanh::lean_dec_ref_known(v___x_3585_, 1);
                                v_currRecDepth_3587_ = crate::leanh::lean_ctor_get(v___y_3567_, 2);
                                v_quotContext_x3f_3588_ =
                                    crate::leanh::lean_ctor_get(v___y_3567_, 5);
                                crate::leanh::lean_inc_ref_n(v_env_3571_, 3);
                                v___f_3589_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                                crate::leanh::lean_closure_set(v___f_3589_, 0, v_env_3571_);
                                v___f_3590_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                                crate::leanh::lean_closure_set(v___f_3590_, 0, v_env_3571_);
                                crate::leanh::lean_inc_n(v_currNamespace_3579_, 2);
                                v___f_3591_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 1);
                                crate::leanh::lean_closure_set(
                                    v___f_3591_,
                                    0,
                                    v_currNamespace_3579_,
                                );
                                crate::leanh::lean_inc(v_openDecls_3582_);
                                v___f_3592_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 3);
                                crate::leanh::lean_closure_set(v___f_3592_, 0, v_env_3571_);
                                crate::leanh::lean_closure_set(
                                    v___f_3592_,
                                    1,
                                    v_currNamespace_3579_,
                                );
                                crate::leanh::lean_closure_set(v___f_3592_, 2, v_openDecls_3582_);
                                v___f_3593_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                                crate::leanh::lean_closure_set(v___f_3593_, 0, v_env_3571_);
                                crate::leanh::lean_closure_set(v___f_3593_, 1, v_opts_3576_);
                                crate::leanh::lean_closure_set(
                                    v___f_3593_,
                                    2,
                                    v_currNamespace_3579_,
                                );
                                crate::leanh::lean_closure_set(v___f_3593_, 3, v_openDecls_3582_);
                                v_methods_3594_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_methods_3594_, 0, v___f_3590_);
                                crate::leanh::lean_ctor_set(v_methods_3594_, 1, v___f_3591_);
                                crate::leanh::lean_ctor_set(v_methods_3594_, 2, v___f_3589_);
                                crate::leanh::lean_ctor_set(v_methods_3594_, 3, v___f_3592_);
                                crate::leanh::lean_ctor_set(v_methods_3594_, 4, v___f_3593_);
                                if crate::leanh::lean_obj_tag(v_quotContext_x3f_3588_) == 0 {
                                    v___x_3668_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_3568_);
                                    v_a_3669_ = crate::leanh::lean_ctor_get(v___x_3668_, 0);
                                    crate::leanh::lean_inc(v_a_3669_);
                                    crate::leanh::lean_dec_ref(v___x_3668_);
                                    v_a_3596_ = v_a_3669_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_3670_ =
                                        crate::leanh::lean_ctor_get(v_quotContext_x3f_3588_, 0);
                                    crate::leanh::lean_inc(v_val_3670_);
                                    v_a_3596_ = v_val_3670_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3584_);
                                crate::leanh::lean_dec(v_openDecls_3582_);
                                crate::leanh::lean_dec(v_currNamespace_3579_);
                                crate::leanh::lean_dec_ref(v_opts_3576_);
                                crate::leanh::lean_dec_ref(v_env_3571_);
                                crate::leanh::lean_dec_ref(v_x_3566_);
                                v_a_3671_ = crate::leanh::lean_ctor_get(v___x_3585_, 0);
                                v_isSharedCheck_3678_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3585_)) as u8;
                                if v_isSharedCheck_3678_ == 0 {
                                    v___x_3673_ = v___x_3585_;
                                    v_isShared_3674_ = v_isSharedCheck_3678_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3671_);
                                    crate::leanh::lean_dec(v___x_3585_);
                                    v___x_3673_ = crate::leanh::lean_box(0);
                                    v_isShared_3674_ = v_isSharedCheck_3678_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_openDecls_3582_);
                            crate::leanh::lean_dec(v_currNamespace_3579_);
                            crate::leanh::lean_dec_ref(v_opts_3576_);
                            crate::leanh::lean_dec_ref(v_env_3571_);
                            crate::leanh::lean_dec_ref(v_x_3566_);
                            v_a_3679_ = crate::leanh::lean_ctor_get(v___x_3583_, 0);
                            v_isSharedCheck_3686_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3583_)) as u8;
                            if v_isSharedCheck_3686_ == 0 {
                                v___x_3681_ = v___x_3583_;
                                v_isShared_3682_ = v_isSharedCheck_3686_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3679_);
                                crate::leanh::lean_dec(v___x_3583_);
                                v___x_3681_ = crate::leanh::lean_box(0);
                                v_isShared_3682_ = v_isSharedCheck_3686_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_currNamespace_3579_);
                        crate::leanh::lean_dec_ref(v_opts_3576_);
                        crate::leanh::lean_dec_ref(v_env_3571_);
                        crate::leanh::lean_dec_ref(v_x_3566_);
                        v_a_3687_ = crate::leanh::lean_ctor_get(v___x_3580_, 0);
                        v_isSharedCheck_3694_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3580_)) as u8;
                        if v_isSharedCheck_3694_ == 0 {
                            v___x_3689_ = v___x_3580_;
                            v_isShared_3690_ = v_isSharedCheck_3694_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3687_);
                            crate::leanh::lean_dec(v___x_3580_);
                            v___x_3689_ = crate::leanh::lean_box(0);
                            v_isShared_3690_ = v_isSharedCheck_3694_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_opts_3576_);
                    crate::leanh::lean_dec_ref(v_env_3571_);
                    crate::leanh::lean_dec_ref(v_x_3566_);
                    v_a_3695_ = crate::leanh::lean_ctor_get(v___x_3577_, 0);
                    v_isSharedCheck_3702_ = (!crate::leanh::lean_is_exclusive(v___x_3577_)) as u8;
                    if v_isSharedCheck_3702_ == 0 {
                        v___x_3697_ = v___x_3577_;
                        v_isShared_3698_ = v_isSharedCheck_3702_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3695_);
                        crate::leanh::lean_dec(v___x_3577_);
                        v___x_3697_ = crate::leanh::lean_box(0);
                        v_isShared_3698_ = v_isSharedCheck_3702_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3597_ = lean_st_ref_get(v___y_3568_);
                v_maxRecDepth_3598_ = crate::leanh::lean_ctor_get(v___x_3597_, 5);
                crate::leanh::lean_inc(v_maxRecDepth_3598_);
                crate::leanh::lean_dec(v___x_3597_);
                v___x_3599_ = lean_st_ref_get(v___y_3568_);
                v_nextMacroScope_3600_ = crate::leanh::lean_ctor_get(v___x_3599_, 4);
                crate::leanh::lean_inc(v_nextMacroScope_3600_);
                crate::leanh::lean_dec(v___x_3599_);
                crate::leanh::lean_inc(v_currRecDepth_3587_);
                v___x_3601_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3601_, 0, v_methods_3594_);
                crate::leanh::lean_ctor_set(v___x_3601_, 1, v_a_3596_);
                crate::leanh::lean_ctor_set(v___x_3601_, 2, v_a_3586_);
                crate::leanh::lean_ctor_set(v___x_3601_, 3, v_currRecDepth_3587_);
                crate::leanh::lean_ctor_set(v___x_3601_, 4, v_maxRecDepth_3598_);
                crate::leanh::lean_ctor_set(v___x_3601_, 5, v_a_3584_);
                v___x_3602_ = crate::leanh::lean_box(0);
                v___x_3603_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3603_, 0, v_nextMacroScope_3600_);
                crate::leanh::lean_ctor_set(v___x_3603_, 1, v___x_3602_);
                crate::leanh::lean_ctor_set(v___x_3603_, 2, v___x_3602_);
                v___x_3604_ = crate::leanh::lean_apply_2(v_x_3566_, v___x_3601_, v___x_3603_);
                if crate::leanh::lean_obj_tag(v___x_3604_) == 0 {
                    v_a_3605_ = crate::leanh::lean_ctor_get(v___x_3604_, 1);
                    crate::leanh::lean_inc(v_a_3605_);
                    v_a_3606_ = crate::leanh::lean_ctor_get(v___x_3604_, 0);
                    crate::leanh::lean_inc(v_a_3606_);
                    crate::leanh::lean_dec_ref_known(v___x_3604_, 2);
                    v_macroScope_3607_ = crate::leanh::lean_ctor_get(v_a_3605_, 0);
                    crate::leanh::lean_inc(v_macroScope_3607_);
                    v_traceMsgs_3608_ = crate::leanh::lean_ctor_get(v_a_3605_, 1);
                    crate::leanh::lean_inc(v_traceMsgs_3608_);
                    v_expandedMacroDecls_3609_ = crate::leanh::lean_ctor_get(v_a_3605_, 2);
                    crate::leanh::lean_inc(v_expandedMacroDecls_3609_);
                    crate::leanh::lean_dec(v_a_3605_);
                    v___x_3610_ = crate::leanh::lean_box(0);
                    v___x_3611_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_expandedMacroDecls_3609_, v___x_3610_, v___y_3567_, v___y_3568_);
                    crate::leanh::lean_dec(v_expandedMacroDecls_3609_);
                    if crate::leanh::lean_obj_tag(v___x_3611_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3611_, 1);
                        v___x_3612_ = lean_st_ref_take(v___y_3568_);
                        v_env_3613_ = crate::leanh::lean_ctor_get(v___x_3612_, 0);
                        v_messages_3614_ = crate::leanh::lean_ctor_get(v___x_3612_, 1);
                        v_scopes_3615_ = crate::leanh::lean_ctor_get(v___x_3612_, 2);
                        v_usedQuotCtxts_3616_ = crate::leanh::lean_ctor_get(v___x_3612_, 3);
                        v_maxRecDepth_3617_ = crate::leanh::lean_ctor_get(v___x_3612_, 5);
                        v_ngen_3618_ = crate::leanh::lean_ctor_get(v___x_3612_, 6);
                        v_auxDeclNGen_3619_ = crate::leanh::lean_ctor_get(v___x_3612_, 7);
                        v_infoState_3620_ = crate::leanh::lean_ctor_get(v___x_3612_, 8);
                        v_traceState_3621_ = crate::leanh::lean_ctor_get(v___x_3612_, 9);
                        v_snapshotTasks_3622_ = crate::leanh::lean_ctor_get(v___x_3612_, 10);
                        v_isSharedCheck_3648_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3612_)) as u8;
                        if v_isSharedCheck_3648_ == 0 {
                            v_unused_3649_ = crate::leanh::lean_ctor_get(v___x_3612_, 4);
                            crate::leanh::lean_dec(v_unused_3649_);
                            v___x_3624_ = v___x_3612_;
                            v_isShared_3625_ = v_isSharedCheck_3648_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_3622_);
                            crate::leanh::lean_inc(v_traceState_3621_);
                            crate::leanh::lean_inc(v_infoState_3620_);
                            crate::leanh::lean_inc(v_auxDeclNGen_3619_);
                            crate::leanh::lean_inc(v_ngen_3618_);
                            crate::leanh::lean_inc(v_maxRecDepth_3617_);
                            crate::leanh::lean_inc(v_usedQuotCtxts_3616_);
                            crate::leanh::lean_inc(v_scopes_3615_);
                            crate::leanh::lean_inc(v_messages_3614_);
                            crate::leanh::lean_inc(v_env_3613_);
                            crate::leanh::lean_dec(v___x_3612_);
                            v___x_3624_ = crate::leanh::lean_box(0);
                            v_isShared_3625_ = v_isSharedCheck_3648_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_traceMsgs_3608_);
                        crate::leanh::lean_dec(v_macroScope_3607_);
                        crate::leanh::lean_dec(v_a_3606_);
                        v_a_3650_ = crate::leanh::lean_ctor_get(v___x_3611_, 0);
                        v_isSharedCheck_3657_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3611_)) as u8;
                        if v_isSharedCheck_3657_ == 0 {
                            v___x_3652_ = v___x_3611_;
                            v_isShared_3653_ = v_isSharedCheck_3657_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3650_);
                            crate::leanh::lean_dec(v___x_3611_);
                            v___x_3652_ = crate::leanh::lean_box(0);
                            v_isShared_3653_ = v_isSharedCheck_3657_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_3658_ = crate::leanh::lean_ctor_get(v___x_3604_, 0);
                    crate::leanh::lean_inc(v_a_3658_);
                    crate::leanh::lean_dec_ref_known(v___x_3604_, 2);
                    if crate::leanh::lean_obj_tag(v_a_3658_) == 0 {
                        v_a_3659_ = crate::leanh::lean_ctor_get(v_a_3658_, 0);
                        crate::leanh::lean_inc(v_a_3659_);
                        v_a_3660_ = crate::leanh::lean_ctor_get(v_a_3658_, 1);
                        crate::leanh::lean_inc_ref(v_a_3660_);
                        crate::leanh::lean_dec_ref_known(v_a_3658_, 2);
                        v___x_3661_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___closed__0;
                        v___x_3662_ = lean_string_dec_eq(v_a_3660_, v___x_3661_);
                        if v___x_3662_ == 0 {
                            v___x_3663_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3663_, 0, v_a_3660_);
                            v___x_3664_ = l_Lean_MessageData_ofFormat(v___x_3663_);
                            v___x_3665_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_a_3659_, v___x_3664_, v___y_3567_, v___y_3568_);
                            crate::leanh::lean_dec(v_a_3659_);
                            return v___x_3665_;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_3660_);
                            v___x_3666_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_a_3659_);
                            return v___x_3666_;
                        }
                    } else {
                        v___x_3667_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
                        return v___x_3667_;
                    }
                }
            }
            2 => {
                if v_isShared_3625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3624_, 4, v_macroScope_3607_);
                    v___x_3627_ = v___x_3624_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3647_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_env_3613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_messages_3614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 2, v_scopes_3615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 3, v_usedQuotCtxts_3616_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 4, v_macroScope_3607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 5, v_maxRecDepth_3617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 6, v_ngen_3618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 7, v_auxDeclNGen_3619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 8, v_infoState_3620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 9, v_traceState_3621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 10, v_snapshotTasks_3622_);
                    v___x_3627_ = v_reuseFailAlloc_3647_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3628_ = lean_st_ref_set(v___y_3568_, v___x_3627_);
                v___x_3629_ = l_List_reverse___redArg(v_traceMsgs_3608_);
                v___x_3630_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__3(v___x_3629_, v___y_3567_, v___y_3568_);
                if crate::leanh::lean_obj_tag(v___x_3630_) == 0 {
                    v_isSharedCheck_3637_ = (!crate::leanh::lean_is_exclusive(v___x_3630_)) as u8;
                    if v_isSharedCheck_3637_ == 0 {
                        v_unused_3638_ = crate::leanh::lean_ctor_get(v___x_3630_, 0);
                        crate::leanh::lean_dec(v_unused_3638_);
                        v___x_3632_ = v___x_3630_;
                        v_isShared_3633_ = v_isSharedCheck_3637_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3630_);
                        v___x_3632_ = crate::leanh::lean_box(0);
                        v_isShared_3633_ = v_isSharedCheck_3637_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3606_);
                    v_a_3639_ = crate::leanh::lean_ctor_get(v___x_3630_, 0);
                    v_isSharedCheck_3646_ = (!crate::leanh::lean_is_exclusive(v___x_3630_)) as u8;
                    if v_isSharedCheck_3646_ == 0 {
                        v___x_3641_ = v___x_3630_;
                        v_isShared_3642_ = v_isSharedCheck_3646_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3639_);
                        crate::leanh::lean_dec(v___x_3630_);
                        v___x_3641_ = crate::leanh::lean_box(0);
                        v_isShared_3642_ = v_isSharedCheck_3646_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3633_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3632_, 0, v_a_3606_);
                    v___x_3635_ = v___x_3632_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3606_);
                    v___x_3635_ = v_reuseFailAlloc_3636_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3635_;
            }
            6 => {
                if v_isShared_3642_ == 0 {
                    v___x_3644_ = v___x_3641_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
                    v___x_3644_ = v_reuseFailAlloc_3645_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3644_;
            }
            8 => {
                if v_isShared_3653_ == 0 {
                    v___x_3655_ = v___x_3652_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
                    v___x_3655_ = v_reuseFailAlloc_3656_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3655_;
            }
            10 => {
                if v_isShared_3674_ == 0 {
                    v___x_3676_ = v___x_3673_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
                    v___x_3676_ = v_reuseFailAlloc_3677_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3676_;
            }
            12 => {
                if v_isShared_3682_ == 0 {
                    v___x_3684_ = v___x_3681_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
                    v___x_3684_ = v_reuseFailAlloc_3685_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3684_;
            }
            14 => {
                if v_isShared_3690_ == 0 {
                    v___x_3692_ = v___x_3689_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3693_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
                    v___x_3692_ = v_reuseFailAlloc_3693_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3692_;
            }
            16 => {
                if v_isShared_3698_ == 0 {
                    v___x_3700_ = v___x_3697_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3701_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
                    v___x_3700_ = v_reuseFailAlloc_3701_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg___boxed(
    mut v_x_3703_: *mut crate::leanh::LeanObject,
    mut v___y_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3707_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(
            v_x_3703_,
            v___y_3704_,
            v___y_3705_,
        );
    crate::leanh::lean_dec(v___y_3705_);
    crate::leanh::lean_dec_ref(v___y_3704_);
    return v_res_3707_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3722_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__6;
    v___x_3723_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3___closed__11;
    v___x_3724_ = l_Lean_Name_append(v___x_3723_, v___x_3722_);
    return v___x_3724_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3726_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__8;
    v___x_3727_ = l_Lean_stringToMessageData(v___x_3726_);
    return v___x_3727_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3729_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__10;
    v___x_3730_ = l_Lean_stringToMessageData(v___x_3729_);
    return v___x_3730_;
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfInstance(
    mut v_modifiers_3731_: *mut crate::leanh::LeanObject,
    mut v_stx_3732_: *mut crate::leanh::LeanObject,
    mut v_a_3733_: *mut crate::leanh::LeanObject,
    mut v_a_3734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declId_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: u8 = 0;
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3801_: u8 = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3831_: u8 = 0;
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: u8 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3846_: u8 = 0;
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut v_a_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3854_: u8 = 0;
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3858_: u8 = 0;
    let mut v_a_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3862_: u8 = 0;
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3866_: u8 = 0;
    let mut v_val_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3875_: u8 = 0;
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: u8 = 0;
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3887_: u8 = 0;
    let mut v___x_3888_: u8 = 0;
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3904_: u8 = 0;
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3908_: u8 = 0;
    let mut v_a_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3916_: u8 = 0;
    let mut v_a_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v_reuseFailAlloc_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_a_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_a_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3947_: u8 = 0;
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3951_: u8 = 0;
    let mut v_a_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3736_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3756_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3736_);
                v___x_3757_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_toAttributeKind___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_3757_, 0, v___x_3756_);
                v___x_3758_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_3757_, v_a_3733_, v_a_3734_);
                if crate::leanh::lean_obj_tag(v___x_3758_) == 0 {
                    v_a_3759_ = crate::leanh::lean_ctor_get(v___x_3758_, 0);
                    crate::leanh::lean_inc(v_a_3759_);
                    crate::leanh::lean_dec_ref_known(v___x_3758_, 1);
                    v___x_3760_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_3783_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3760_);
                    v___x_3784_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_expandOptNamedPrio___boxed as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_3784_, 0, v___x_3783_);
                    v___x_3785_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(v___x_3784_, v_a_3733_, v_a_3734_);
                    if crate::leanh::lean_obj_tag(v___x_3785_) == 0 {
                        v_a_3786_ = crate::leanh::lean_ctor_get(v___x_3785_, 0);
                        crate::leanh::lean_inc(v_a_3786_);
                        crate::leanh::lean_dec_ref_known(v___x_3785_, 1);
                        v___x_3787_ = l_Lean_Elab_Command_getRef___redArg(v_a_3733_);
                        if crate::leanh::lean_obj_tag(v___x_3787_) == 0 {
                            v_a_3788_ = crate::leanh::lean_ctor_get(v___x_3787_, 0);
                            crate::leanh::lean_inc(v_a_3788_);
                            crate::leanh::lean_dec_ref_known(v___x_3787_, 1);
                            v___x_3789_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_3733_);
                            if crate::leanh::lean_obj_tag(v___x_3789_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3789_, 1);
                                v_quotContext_x3f_3790_ = crate::leanh::lean_ctor_get(v_a_3733_, 5);
                                v___x_3791_ = 0;
                                v___x_3792_ = l_Lean_SourceInfo_fromRef(v_a_3788_, v___x_3791_);
                                crate::leanh::lean_dec(v_a_3788_);
                                if crate::leanh::lean_obj_tag(v_quotContext_x3f_3790_) == 0 {
                                    v___x_3927_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_3734_);
                                    crate::leanh::lean_dec_ref(v___x_3927_);
                                    state = 3;
                                    continue;
                                } else {
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3788_);
                                crate::leanh::lean_dec(v_a_3786_);
                                crate::leanh::lean_dec(v_a_3759_);
                                crate::leanh::lean_dec(v_stx_3732_);
                                crate::leanh::lean_dec_ref(v_modifiers_3731_);
                                v_a_3928_ = crate::leanh::lean_ctor_get(v___x_3789_, 0);
                                v_isSharedCheck_3935_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3789_)) as u8;
                                if v_isSharedCheck_3935_ == 0 {
                                    v___x_3930_ = v___x_3789_;
                                    v_isShared_3931_ = v_isSharedCheck_3935_;
                                    state = 18;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3928_);
                                    crate::leanh::lean_dec(v___x_3789_);
                                    v___x_3930_ = crate::leanh::lean_box(0);
                                    v_isShared_3931_ = v_isSharedCheck_3935_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3786_);
                            crate::leanh::lean_dec(v_a_3759_);
                            crate::leanh::lean_dec(v_stx_3732_);
                            crate::leanh::lean_dec_ref(v_modifiers_3731_);
                            v_a_3936_ = crate::leanh::lean_ctor_get(v___x_3787_, 0);
                            v_isSharedCheck_3943_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3787_)) as u8;
                            if v_isSharedCheck_3943_ == 0 {
                                v___x_3938_ = v___x_3787_;
                                v_isShared_3939_ = v_isSharedCheck_3943_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3936_);
                                crate::leanh::lean_dec(v___x_3787_);
                                v___x_3938_ = crate::leanh::lean_box(0);
                                v_isShared_3939_ = v_isSharedCheck_3943_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3759_);
                        crate::leanh::lean_dec(v_stx_3732_);
                        crate::leanh::lean_dec_ref(v_modifiers_3731_);
                        v_a_3944_ = crate::leanh::lean_ctor_get(v___x_3785_, 0);
                        v_isSharedCheck_3951_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3785_)) as u8;
                        if v_isSharedCheck_3951_ == 0 {
                            v___x_3946_ = v___x_3785_;
                            v_isShared_3947_ = v_isSharedCheck_3951_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3944_);
                            crate::leanh::lean_dec(v___x_3785_);
                            v___x_3946_ = crate::leanh::lean_box(0);
                            v_isShared_3947_ = v_isSharedCheck_3951_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_3732_);
                    crate::leanh::lean_dec_ref(v_modifiers_3731_);
                    v_a_3952_ = crate::leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3959_ = (!crate::leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3959_ == 0 {
                        v___x_3954_ = v___x_3758_;
                        v_isShared_3955_ = v_isSharedCheck_3959_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3952_);
                        crate::leanh::lean_dec(v___x_3758_);
                        v___x_3954_ = crate::leanh::lean_box(0);
                        v_isShared_3955_ = v_isSharedCheck_3959_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                v_docString_x3f_3744_ = crate::leanh::lean_ctor_get(v___y_3740_, 1);
                crate::leanh::lean_inc(v_docString_x3f_3744_);
                v___x_3745_ = 1;
                v___x_3746_ = l_Lean_Syntax_getArgs(v_stx_3732_);
                v___x_3747_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_3748_ = l_Array_toSubarray___redArg(v___x_3746_, v___x_3736_, v___x_3747_);
                v___x_3749_ = l_Subarray_copy___redArg(v___x_3748_);
                v___x_3750_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3750_, 0, v___y_3738_);
                crate::leanh::lean_ctor_set(v___x_3750_, 1, v___y_3741_);
                crate::leanh::lean_ctor_set(v___x_3750_, 2, v___x_3749_);
                v___x_3751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3751_, 0, v___y_3739_);
                v___x_3752_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3747_);
                v___x_3753_ = crate::leanh::lean_box(0);
                v___x_3754_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3754_, 0, v_stx_3732_);
                crate::leanh::lean_ctor_set(v___x_3754_, 1, v___x_3750_);
                crate::leanh::lean_ctor_set(v___x_3754_, 2, v___y_3740_);
                crate::leanh::lean_ctor_set(v___x_3754_, 3, v_declId_3743_);
                crate::leanh::lean_ctor_set(v___x_3754_, 4, v___y_3742_);
                crate::leanh::lean_ctor_set(v___x_3754_, 5, v___x_3751_);
                crate::leanh::lean_ctor_set(v___x_3754_, 6, v___x_3752_);
                crate::leanh::lean_ctor_set(v___x_3754_, 7, v_docString_x3f_3744_);
                crate::leanh::lean_ctor_set(v___x_3754_, 8, v___x_3753_);
                crate::leanh::lean_ctor_set(v___x_3754_, 9, v___x_3753_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3754_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    v___x_3745_,
                );
                v___x_3755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3755_, 0, v___x_3754_);
                return v___x_3755_;
            }
            2 => {
                v___x_3770_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__0;
                v___x_3771_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__1;
                crate::leanh::lean_inc_ref(v___y_3764_);
                crate::leanh::lean_inc_ref(v___y_3768_);
                v___x_3772_ =
                    l_Lean_Name_mkStr4(v___y_3768_, v___y_3764_, v___x_3770_, v___x_3771_);
                v___x_3773_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3774_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3773_);
                v___x_3775_ = 1;
                v___x_3776_ = l_Lean_mkIdentFrom(v___x_3774_, v___y_3765_, v___x_3775_);
                crate::leanh::lean_dec(v___x_3774_);
                v___x_3777_ = l_Lean_Elab_instInhabitedDefViewElabHeaderData_default___closed__0;
                crate::leanh::lean_inc(v___y_3767_);
                crate::leanh::lean_inc_n(v___y_3762_, 2);
                v___x_3778_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3778_, 0, v___y_3762_);
                crate::leanh::lean_ctor_set(v___x_3778_, 1, v___y_3767_);
                crate::leanh::lean_ctor_set(v___x_3778_, 2, v___x_3777_);
                v___x_3779_ = lean_mk_empty_array_with_capacity(v___x_3760_);
                v___x_3780_ = lean_array_push(v___x_3779_, v___x_3776_);
                v___x_3781_ = lean_array_push(v___x_3780_, v___x_3778_);
                v___x_3782_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3782_, 0, v___y_3762_);
                crate::leanh::lean_ctor_set(v___x_3782_, 1, v___x_3772_);
                crate::leanh::lean_ctor_set(v___x_3782_, 2, v___x_3781_);
                v___y_3738_ = v___y_3762_;
                v___y_3739_ = v___y_3763_;
                v___y_3740_ = v___y_3766_;
                v___y_3741_ = v___y_3767_;
                v___y_3742_ = v___y_3769_;
                v_declId_3743_ = v___x_3782_;
                state = 1;
                continue;
            }
            3 => {
                v___x_3794_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3795_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3794_);
                v___x_3796_ = l_Lean_Elab_expandDeclSig(v___x_3795_);
                crate::leanh::lean_dec(v___x_3795_);
                v_fst_3797_ = crate::leanh::lean_ctor_get(v___x_3796_, 0);
                v_snd_3798_ = crate::leanh::lean_ctor_get(v___x_3796_, 1);
                v_isSharedCheck_3926_ = (!crate::leanh::lean_is_exclusive(v___x_3796_)) as u8;
                if v_isSharedCheck_3926_ == 0 {
                    v___x_3800_ = v___x_3796_;
                    v_isShared_3801_ = v_isSharedCheck_3926_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3798_);
                    crate::leanh::lean_inc(v_fst_3797_);
                    crate::leanh::lean_dec(v___x_3796_);
                    v___x_3800_ = crate::leanh::lean_box(0);
                    v_isShared_3801_ = v_isSharedCheck_3926_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3802_ = l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_DefView_2042677648____hygCtx___hyg_20_;
                v___x_3803_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__2;
                v___x_3804_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__0;
                v___x_3805_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__4;
                crate::leanh::lean_inc(v___x_3792_);
                if v_isShared_3801_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3800_, 2);
                    crate::leanh::lean_ctor_set(v___x_3800_, 1, v___x_3804_);
                    crate::leanh::lean_ctor_set(v___x_3800_, 0, v___x_3792_);
                    v___x_3807_ = v___x_3800_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 1, v___x_3804_);
                    v___x_3807_ = v_reuseFailAlloc_3925_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3808_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_3809_ = l_Nat_reprFast(v_a_3786_);
                v___x_3810_ = crate::leanh::lean_box(2);
                v___x_3811_ = l_Lean_Syntax_mkNumLit(v___x_3809_, v___x_3810_);
                crate::leanh::lean_inc(v___x_3792_);
                v___x_3812_ = l_Lean_Syntax_node1(v___x_3792_, v___x_3808_, v___x_3811_);
                v___x_3813_ =
                    l_Lean_Syntax_node2(v___x_3792_, v___x_3805_, v___x_3807_, v___x_3812_);
                v___x_3814_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_DefView_isInstance_spec__0___closed__1;
                v___x_3815_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3815_, 0, v___x_3814_);
                crate::leanh::lean_ctor_set(v___x_3815_, 1, v___x_3813_);
                v___x_3816_ = (crate::leanh::lean_unbox(v_a_3759_) as u8);
                crate::leanh::lean_dec(v_a_3759_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3815_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3816_,
                );
                v___x_3817_ = l_Lean_Elab_Modifiers_addAttr(v_modifiers_3731_, v___x_3815_);
                v___x_3818_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3819_ = l_Lean_Syntax_getArg(v_stx_3732_, v___x_3818_);
                v___x_3820_ = l_Lean_Syntax_getOptional_x3f(v___x_3819_);
                crate::leanh::lean_dec(v___x_3819_);
                if crate::leanh::lean_obj_tag(v___x_3820_) == 0 {
                    v___x_3821_ = l_Lean_Syntax_getArgs(v_fst_3797_);
                    crate::leanh::lean_inc(v_snd_3798_);
                    v___x_3822_ = l_Lean_Elab_Command_mkInstanceName(
                        v___x_3821_,
                        v_snd_3798_,
                        v_a_3733_,
                        v_a_3734_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3822_) == 0 {
                        v_a_3823_ = crate::leanh::lean_ctor_get(v___x_3822_, 0);
                        crate::leanh::lean_inc(v_a_3823_);
                        crate::leanh::lean_dec_ref_known(v___x_3822_, 1);
                        v___x_3824_ = l_Lean_inheritedTraceOptions;
                        v___x_3825_ = lean_st_ref_get(v___x_3824_);
                        v___x_3826_ = lean_st_ref_get(v_a_3734_);
                        v_scopes_3827_ = crate::leanh::lean_ctor_get(v___x_3826_, 2);
                        crate::leanh::lean_inc(v_scopes_3827_);
                        crate::leanh::lean_dec(v___x_3826_);
                        v___x_3828_ = l_Lean_Elab_Command_instInhabitedScope_default;
                        v___x_3829_ = l_List_head_x21___redArg(v___x_3828_, v_scopes_3827_);
                        crate::leanh::lean_dec(v_scopes_3827_);
                        v_opts_3830_ = crate::leanh::lean_ctor_get(v___x_3829_, 1);
                        crate::leanh::lean_inc_ref(v_opts_3830_);
                        crate::leanh::lean_dec(v___x_3829_);
                        v_hasTrace_3831_ = crate::leanh::lean_ctor_get_uint8(
                            v_opts_3830_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3831_ == 0 {
                            crate::leanh::lean_dec_ref(v_opts_3830_);
                            crate::leanh::lean_dec(v___x_3825_);
                            v___y_3762_ = v___x_3810_;
                            v___y_3763_ = v_snd_3798_;
                            v___y_3764_ = v___x_3803_;
                            v___y_3765_ = v_a_3823_;
                            v___y_3766_ = v___x_3817_;
                            v___y_3767_ = v___x_3808_;
                            v___y_3768_ = v___x_3802_;
                            v___y_3769_ = v_fst_3797_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3832_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__6;
                            v___x_3833_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_mkDefViewOfInstance___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once
                                ),
                                _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7,
                            );
                            v___x_3834_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v___x_3825_,
                                v_opts_3830_,
                                v___x_3833_,
                            );
                            crate::leanh::lean_dec_ref(v_opts_3830_);
                            crate::leanh::lean_dec(v___x_3825_);
                            if v___x_3834_ == 0 {
                                v___y_3762_ = v___x_3810_;
                                v___y_3763_ = v_snd_3798_;
                                v___y_3764_ = v___x_3803_;
                                v___y_3765_ = v_a_3823_;
                                v___y_3766_ = v___x_3817_;
                                v___y_3767_ = v___x_3808_;
                                v___y_3768_ = v___x_3802_;
                                v___y_3769_ = v_fst_3797_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3835_ = l_Lean_Elab_Command_getScope___redArg(v_a_3734_);
                                if crate::leanh::lean_obj_tag(v___x_3835_) == 0 {
                                    v_a_3836_ = crate::leanh::lean_ctor_get(v___x_3835_, 0);
                                    crate::leanh::lean_inc(v_a_3836_);
                                    crate::leanh::lean_dec_ref_known(v___x_3835_, 1);
                                    v_currNamespace_3837_ =
                                        crate::leanh::lean_ctor_get(v_a_3836_, 2);
                                    crate::leanh::lean_inc(v_currNamespace_3837_);
                                    crate::leanh::lean_dec(v_a_3836_);
                                    v___x_3838_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once), _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
                                    crate::leanh::lean_inc(v_a_3823_);
                                    v___x_3839_ =
                                        l_Lean_Name_append(v_currNamespace_3837_, v_a_3823_);
                                    v___x_3840_ = l_Lean_MessageData_ofName(v___x_3839_);
                                    v___x_3841_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3841_, 0, v___x_3838_);
                                    crate::leanh::lean_ctor_set(v___x_3841_, 1, v___x_3840_);
                                    v___x_3842_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_3832_, v___x_3841_, v_a_3733_, v_a_3734_);
                                    if crate::leanh::lean_obj_tag(v___x_3842_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3842_, 1);
                                        v___y_3762_ = v___x_3810_;
                                        v___y_3763_ = v_snd_3798_;
                                        v___y_3764_ = v___x_3803_;
                                        v___y_3765_ = v_a_3823_;
                                        v___y_3766_ = v___x_3817_;
                                        v___y_3767_ = v___x_3808_;
                                        v___y_3768_ = v___x_3802_;
                                        v___y_3769_ = v_fst_3797_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_3823_);
                                        crate::leanh::lean_dec_ref(v___x_3817_);
                                        crate::leanh::lean_dec(v_snd_3798_);
                                        crate::leanh::lean_dec(v_fst_3797_);
                                        crate::leanh::lean_dec(v_stx_3732_);
                                        v_a_3843_ = crate::leanh::lean_ctor_get(v___x_3842_, 0);
                                        v_isSharedCheck_3850_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3842_)) as u8;
                                        if v_isSharedCheck_3850_ == 0 {
                                            v___x_3845_ = v___x_3842_;
                                            v_isShared_3846_ = v_isSharedCheck_3850_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3843_);
                                            crate::leanh::lean_dec(v___x_3842_);
                                            v___x_3845_ = crate::leanh::lean_box(0);
                                            v_isShared_3846_ = v_isSharedCheck_3850_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3823_);
                                    crate::leanh::lean_dec_ref(v___x_3817_);
                                    crate::leanh::lean_dec(v_snd_3798_);
                                    crate::leanh::lean_dec(v_fst_3797_);
                                    crate::leanh::lean_dec(v_stx_3732_);
                                    v_a_3851_ = crate::leanh::lean_ctor_get(v___x_3835_, 0);
                                    v_isSharedCheck_3858_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3835_)) as u8;
                                    if v_isSharedCheck_3858_ == 0 {
                                        v___x_3853_ = v___x_3835_;
                                        v_isShared_3854_ = v_isSharedCheck_3858_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3851_);
                                        crate::leanh::lean_dec(v___x_3835_);
                                        v___x_3853_ = crate::leanh::lean_box(0);
                                        v_isShared_3854_ = v_isSharedCheck_3858_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3817_);
                        crate::leanh::lean_dec(v_snd_3798_);
                        crate::leanh::lean_dec(v_fst_3797_);
                        crate::leanh::lean_dec(v_stx_3732_);
                        v_a_3859_ = crate::leanh::lean_ctor_get(v___x_3822_, 0);
                        v_isSharedCheck_3866_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3822_)) as u8;
                        if v_isSharedCheck_3866_ == 0 {
                            v___x_3861_ = v___x_3822_;
                            v_isShared_3862_ = v_isSharedCheck_3866_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3859_);
                            crate::leanh::lean_dec(v___x_3822_);
                            v___x_3861_ = crate::leanh::lean_box(0);
                            v_isShared_3862_ = v_isSharedCheck_3866_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v_val_3867_ = crate::leanh::lean_ctor_get(v___x_3820_, 0);
                    crate::leanh::lean_inc(v_val_3867_);
                    crate::leanh::lean_dec_ref_known(v___x_3820_, 1);
                    v___x_3868_ = l_Lean_inheritedTraceOptions;
                    v___x_3869_ = lean_st_ref_get(v___x_3868_);
                    v___x_3870_ = lean_st_ref_get(v_a_3734_);
                    v_scopes_3871_ = crate::leanh::lean_ctor_get(v___x_3870_, 2);
                    crate::leanh::lean_inc(v_scopes_3871_);
                    crate::leanh::lean_dec(v___x_3870_);
                    v___x_3872_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_3873_ = l_List_head_x21___redArg(v___x_3872_, v_scopes_3871_);
                    crate::leanh::lean_dec(v_scopes_3871_);
                    v_opts_3874_ = crate::leanh::lean_ctor_get(v___x_3873_, 1);
                    crate::leanh::lean_inc_ref(v_opts_3874_);
                    crate::leanh::lean_dec(v___x_3873_);
                    v_hasTrace_3875_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_3874_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3875_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_3874_);
                        crate::leanh::lean_dec(v___x_3869_);
                        v___y_3738_ = v___x_3810_;
                        v___y_3739_ = v_snd_3798_;
                        v___y_3740_ = v___x_3817_;
                        v___y_3741_ = v___x_3808_;
                        v___y_3742_ = v_fst_3797_;
                        v_declId_3743_ = v_val_3867_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3876_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__6;
                        v___x_3877_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_mkDefViewOfInstance___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_mkDefViewOfInstance___closed__7_once
                            ),
                            _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__7,
                        );
                        v___x_3878_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_3869_,
                            v_opts_3874_,
                            v___x_3877_,
                        );
                        crate::leanh::lean_dec_ref(v_opts_3874_);
                        crate::leanh::lean_dec(v___x_3869_);
                        if v___x_3878_ == 0 {
                            v___y_3738_ = v___x_3810_;
                            v___y_3739_ = v_snd_3798_;
                            v___y_3740_ = v___x_3817_;
                            v___y_3741_ = v___x_3808_;
                            v___y_3742_ = v_fst_3797_;
                            v_declId_3743_ = v_val_3867_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3879_ = l_Lean_Syntax_getArgs(v_fst_3797_);
                            crate::leanh::lean_inc(v_snd_3798_);
                            v___x_3880_ = l_Lean_Elab_Command_mkInstanceName(
                                v___x_3879_,
                                v_snd_3798_,
                                v_a_3733_,
                                v_a_3734_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3880_) == 0 {
                                v_a_3881_ = crate::leanh::lean_ctor_get(v___x_3880_, 0);
                                crate::leanh::lean_inc(v_a_3881_);
                                crate::leanh::lean_dec_ref_known(v___x_3880_, 1);
                                v___x_3882_ = lean_st_ref_get(v___x_3868_);
                                v___x_3883_ = lean_st_ref_get(v_a_3734_);
                                v_scopes_3884_ = crate::leanh::lean_ctor_get(v___x_3883_, 2);
                                crate::leanh::lean_inc(v_scopes_3884_);
                                crate::leanh::lean_dec(v___x_3883_);
                                v___x_3885_ = l_List_head_x21___redArg(v___x_3872_, v_scopes_3884_);
                                crate::leanh::lean_dec(v_scopes_3884_);
                                v_opts_3886_ = crate::leanh::lean_ctor_get(v___x_3885_, 1);
                                crate::leanh::lean_inc_ref(v_opts_3886_);
                                crate::leanh::lean_dec(v___x_3885_);
                                v_hasTrace_3887_ = crate::leanh::lean_ctor_get_uint8(
                                    v_opts_3886_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                );
                                if v_hasTrace_3887_ == 0 {
                                    crate::leanh::lean_dec_ref(v_opts_3886_);
                                    crate::leanh::lean_dec(v___x_3882_);
                                    crate::leanh::lean_dec(v_a_3881_);
                                    v___y_3738_ = v___x_3810_;
                                    v___y_3739_ = v_snd_3798_;
                                    v___y_3740_ = v___x_3817_;
                                    v___y_3741_ = v___x_3808_;
                                    v___y_3742_ = v_fst_3797_;
                                    v_declId_3743_ = v_val_3867_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3888_ =
                                        l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                            v___x_3882_,
                                            v_opts_3886_,
                                            v___x_3877_,
                                        );
                                    crate::leanh::lean_dec_ref(v_opts_3886_);
                                    crate::leanh::lean_dec(v___x_3882_);
                                    if v___x_3888_ == 0 {
                                        crate::leanh::lean_dec(v_a_3881_);
                                        v___y_3738_ = v___x_3810_;
                                        v___y_3739_ = v_snd_3798_;
                                        v___y_3740_ = v___x_3817_;
                                        v___y_3741_ = v___x_3808_;
                                        v___y_3742_ = v_fst_3797_;
                                        v_declId_3743_ = v_val_3867_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3889_ =
                                            l_Lean_Elab_Command_getScope___redArg(v_a_3734_);
                                        if crate::leanh::lean_obj_tag(v___x_3889_) == 0 {
                                            v_a_3890_ = crate::leanh::lean_ctor_get(v___x_3889_, 0);
                                            crate::leanh::lean_inc(v_a_3890_);
                                            crate::leanh::lean_dec_ref_known(v___x_3889_, 1);
                                            v_currNamespace_3891_ =
                                                crate::leanh::lean_ctor_get(v_a_3890_, 2);
                                            crate::leanh::lean_inc(v_currNamespace_3891_);
                                            crate::leanh::lean_dec(v_a_3890_);
                                            v___x_3892_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__9_once), _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__9);
                                            v___x_3893_ = l_Lean_Name_append(
                                                v_currNamespace_3891_,
                                                v_a_3881_,
                                            );
                                            v___x_3894_ = l_Lean_MessageData_ofName(v___x_3893_);
                                            v___x_3895_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3895_,
                                                0,
                                                v___x_3892_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3895_,
                                                1,
                                                v___x_3894_,
                                            );
                                            v___x_3896_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfInstance___closed__11_once), _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__11);
                                            v___x_3897_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3897_,
                                                0,
                                                v___x_3895_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3897_,
                                                1,
                                                v___x_3896_,
                                            );
                                            crate::leanh::lean_inc(v_val_3867_);
                                            v___x_3898_ = l_Lean_MessageData_ofSyntax(v_val_3867_);
                                            v___x_3899_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3899_,
                                                0,
                                                v___x_3897_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3899_,
                                                1,
                                                v___x_3898_,
                                            );
                                            v___x_3900_ = l_Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1(v___x_3876_, v___x_3899_, v_a_3733_, v_a_3734_);
                                            if crate::leanh::lean_obj_tag(v___x_3900_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_3900_, 1);
                                                v___y_3738_ = v___x_3810_;
                                                v___y_3739_ = v_snd_3798_;
                                                v___y_3740_ = v___x_3817_;
                                                v___y_3741_ = v___x_3808_;
                                                v___y_3742_ = v_fst_3797_;
                                                v_declId_3743_ = v_val_3867_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_val_3867_);
                                                crate::leanh::lean_dec_ref(v___x_3817_);
                                                crate::leanh::lean_dec(v_snd_3798_);
                                                crate::leanh::lean_dec(v_fst_3797_);
                                                crate::leanh::lean_dec(v_stx_3732_);
                                                v_a_3901_ =
                                                    crate::leanh::lean_ctor_get(v___x_3900_, 0);
                                                v_isSharedCheck_3908_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3900_))
                                                        as u8;
                                                if v_isSharedCheck_3908_ == 0 {
                                                    v___x_3903_ = v___x_3900_;
                                                    v_isShared_3904_ = v_isSharedCheck_3908_;
                                                    state = 12;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3901_);
                                                    crate::leanh::lean_dec(v___x_3900_);
                                                    v___x_3903_ = crate::leanh::lean_box(0);
                                                    v_isShared_3904_ = v_isSharedCheck_3908_;
                                                    state = 12;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_3881_);
                                            crate::leanh::lean_dec(v_val_3867_);
                                            crate::leanh::lean_dec_ref(v___x_3817_);
                                            crate::leanh::lean_dec(v_snd_3798_);
                                            crate::leanh::lean_dec(v_fst_3797_);
                                            crate::leanh::lean_dec(v_stx_3732_);
                                            v_a_3909_ = crate::leanh::lean_ctor_get(v___x_3889_, 0);
                                            v_isSharedCheck_3916_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3889_))
                                                    as u8;
                                            if v_isSharedCheck_3916_ == 0 {
                                                v___x_3911_ = v___x_3889_;
                                                v_isShared_3912_ = v_isSharedCheck_3916_;
                                                state = 14;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3909_);
                                                crate::leanh::lean_dec(v___x_3889_);
                                                v___x_3911_ = crate::leanh::lean_box(0);
                                                v_isShared_3912_ = v_isSharedCheck_3916_;
                                                state = 14;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_3867_);
                                crate::leanh::lean_dec_ref(v___x_3817_);
                                crate::leanh::lean_dec(v_snd_3798_);
                                crate::leanh::lean_dec(v_fst_3797_);
                                crate::leanh::lean_dec(v_stx_3732_);
                                v_a_3917_ = crate::leanh::lean_ctor_get(v___x_3880_, 0);
                                v_isSharedCheck_3924_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3880_)) as u8;
                                if v_isSharedCheck_3924_ == 0 {
                                    v___x_3919_ = v___x_3880_;
                                    v_isShared_3920_ = v_isSharedCheck_3924_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3917_);
                                    crate::leanh::lean_dec(v___x_3880_);
                                    v___x_3919_ = crate::leanh::lean_box(0);
                                    v_isShared_3920_ = v_isSharedCheck_3924_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_3846_ == 0 {
                    v___x_3848_ = v___x_3845_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3849_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
                    v___x_3848_ = v_reuseFailAlloc_3849_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3848_;
            }
            8 => {
                if v_isShared_3854_ == 0 {
                    v___x_3856_ = v___x_3853_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
                    v___x_3856_ = v_reuseFailAlloc_3857_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3856_;
            }
            10 => {
                if v_isShared_3862_ == 0 {
                    v___x_3864_ = v___x_3861_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
                    v___x_3864_ = v_reuseFailAlloc_3865_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3864_;
            }
            12 => {
                if v_isShared_3904_ == 0 {
                    v___x_3906_ = v___x_3903_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
                    v___x_3906_ = v_reuseFailAlloc_3907_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3906_;
            }
            14 => {
                if v_isShared_3912_ == 0 {
                    v___x_3914_ = v___x_3911_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3915_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
                    v___x_3914_ = v_reuseFailAlloc_3915_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3914_;
            }
            16 => {
                if v_isShared_3920_ == 0 {
                    v___x_3922_ = v___x_3919_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
                    v___x_3922_ = v_reuseFailAlloc_3923_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3922_;
            }
            18 => {
                if v_isShared_3931_ == 0 {
                    v___x_3933_ = v___x_3930_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
                    v___x_3933_ = v_reuseFailAlloc_3934_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3933_;
            }
            20 => {
                if v_isShared_3939_ == 0 {
                    v___x_3941_ = v___x_3938_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
                    v___x_3941_ = v_reuseFailAlloc_3942_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3941_;
            }
            22 => {
                if v_isShared_3947_ == 0 {
                    v___x_3949_ = v___x_3946_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
                    v___x_3949_ = v_reuseFailAlloc_3950_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3949_;
            }
            24 => {
                if v_isShared_3955_ == 0 {
                    v___x_3957_ = v___x_3954_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
                    v___x_3957_ = v_reuseFailAlloc_3958_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfInstance___boxed(
    mut v_modifiers_3960_: *mut crate::leanh::LeanObject,
    mut v_stx_3961_: *mut crate::leanh::LeanObject,
    mut v_a_3962_: *mut crate::leanh::LeanObject,
    mut v_a_3963_: *mut crate::leanh::LeanObject,
    mut v_a_3964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3965_ = l_Lean_Elab_Command_mkDefViewOfInstance(
        v_modifiers_3960_,
        v_stx_3961_,
        v_a_3962_,
        v_a_3963_,
    );
    crate::leanh::lean_dec(v_a_3963_);
    crate::leanh::lean_dec_ref(v_a_3962_);
    return v_res_3965_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(
    mut v_00_u03b1_3966_: *mut crate::leanh::LeanObject,
    mut v_x_3967_: *mut crate::leanh::LeanObject,
    mut v___y_3968_: *mut crate::leanh::LeanObject,
    mut v___y_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3970_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___redArg(v_x_3967_, v___y_3969_);
    return v___x_3970_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0___boxed(
    mut v_00_u03b1_3971_: *mut crate::leanh::LeanObject,
    mut v_x_3972_: *mut crate::leanh::LeanObject,
    mut v___y_3973_: *mut crate::leanh::LeanObject,
    mut v___y_3974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3975_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__0(v_00_u03b1_3971_, v_x_3972_, v___y_3973_, v___y_3974_);
    crate::leanh::lean_dec_ref(v___y_3973_);
    crate::leanh::lean_dec_ref(v_x_3972_);
    return v_res_3975_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(
    mut v_00_u03b1_3976_: *mut crate::leanh::LeanObject,
    mut v_ref_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
    mut v___y_3979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3981_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___redArg(v_ref_3977_);
    return v___x_3981_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5___boxed(
    mut v_00_u03b1_3982_: *mut crate::leanh::LeanObject,
    mut v_ref_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__5(v_00_u03b1_3982_, v_ref_3983_, v___y_3984_, v___y_3985_);
    crate::leanh::lean_dec(v___y_3985_);
    crate::leanh::lean_dec_ref(v___y_3984_);
    return v_res_3987_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(
    mut v_00_u03b1_3988_: *mut crate::leanh::LeanObject,
    mut v___y_3989_: *mut crate::leanh::LeanObject,
    mut v___y_3990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3992_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___redArg();
    return v___x_3992_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6___boxed(
    mut v_00_u03b1_3993_: *mut crate::leanh::LeanObject,
    mut v___y_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
    mut v___y_3996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3997_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__6(v_00_u03b1_3993_, v___y_3994_, v___y_3995_);
    crate::leanh::lean_dec(v___y_3995_);
    crate::leanh::lean_dec_ref(v___y_3994_);
    return v_res_3997_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(
    mut v_00_u03b1_3998_: *mut crate::leanh::LeanObject,
    mut v_x_3999_: *mut crate::leanh::LeanObject,
    mut v___y_4000_: *mut crate::leanh::LeanObject,
    mut v___y_4001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4003_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___redArg(
            v_x_3999_,
            v___y_4000_,
            v___y_4001_,
        );
    return v___x_4003_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0___boxed(
    mut v_00_u03b1_4004_: *mut crate::leanh::LeanObject,
    mut v_x_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4009_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0(
        v_00_u03b1_4004_,
        v_x_4005_,
        v___y_4006_,
        v___y_4007_,
    );
    crate::leanh::lean_dec(v___y_4007_);
    crate::leanh::lean_dec_ref(v___y_4006_);
    return v_res_4009_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(
    mut v_msgData_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4014_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___redArg(v_msgData_4010_, v___y_4012_);
    return v___x_4014_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8___boxed(
    mut v_msgData_4015_: *mut crate::leanh::LeanObject,
    mut v___y_4016_: *mut crate::leanh::LeanObject,
    mut v___y_4017_: *mut crate::leanh::LeanObject,
    mut v___y_4018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4019_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__1_spec__8(v_msgData_4015_, v___y_4016_, v___y_4017_);
    crate::leanh::lean_dec(v___y_4017_);
    crate::leanh::lean_dec_ref(v___y_4016_);
    return v_res_4019_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(
    mut v_as_4020_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4021_: *mut crate::leanh::LeanObject,
    mut v_b_4022_: *mut crate::leanh::LeanObject,
    mut v_a_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4027_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___redArg(v_as_x27_4021_, v_b_4022_, v___y_4024_, v___y_4025_);
    return v___x_4027_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2___boxed(
    mut v_as_4028_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4029_: *mut crate::leanh::LeanObject,
    mut v_b_4030_: *mut crate::leanh::LeanObject,
    mut v_a_4031_: *mut crate::leanh::LeanObject,
    mut v___y_4032_: *mut crate::leanh::LeanObject,
    mut v___y_4033_: *mut crate::leanh::LeanObject,
    mut v___y_4034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4035_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__2(v_as_4028_, v_as_x27_4029_, v_b_4030_, v_a_4031_, v___y_4032_, v___y_4033_);
    crate::leanh::lean_dec(v___y_4033_);
    crate::leanh::lean_dec_ref(v___y_4032_);
    crate::leanh::lean_dec(v_as_x27_4029_);
    crate::leanh::lean_dec(v_as_4028_);
    return v_res_4035_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(
    mut v_00_u03b1_4036_: *mut crate::leanh::LeanObject,
    mut v_ref_4037_: *mut crate::leanh::LeanObject,
    mut v_msg_4038_: *mut crate::leanh::LeanObject,
    mut v___y_4039_: *mut crate::leanh::LeanObject,
    mut v___y_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4042_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___redArg(v_ref_4037_, v_msg_4038_, v___y_4039_, v___y_4040_);
    return v___x_4042_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4___boxed(
    mut v_00_u03b1_4043_: *mut crate::leanh::LeanObject,
    mut v_ref_4044_: *mut crate::leanh::LeanObject,
    mut v_msg_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4049_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4(v_00_u03b1_4043_, v_ref_4044_, v_msg_4045_, v___y_4046_, v___y_4047_);
    crate::leanh::lean_dec(v___y_4047_);
    crate::leanh::lean_dec_ref(v___y_4046_);
    crate::leanh::lean_dec(v_ref_4044_);
    return v_res_4049_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(
    mut v_00_u03b2_4050_: *mut crate::leanh::LeanObject,
    mut v_m_4051_: *mut crate::leanh::LeanObject,
    mut v_a_4052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4053_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___redArg(v_m_4051_, v_a_4052_);
    return v___x_4053_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b2_4054_: *mut crate::leanh::LeanObject,
    mut v_m_4055_: *mut crate::leanh::LeanObject,
    mut v_a_4056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5(v_00_u03b2_4054_, v_m_4055_, v_a_4056_);
    crate::leanh::lean_dec(v_a_4056_);
    crate::leanh::lean_dec_ref(v_m_4055_);
    return v_res_4057_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(
    mut v_00_u03b1_4058_: *mut crate::leanh::LeanObject,
    mut v_msg_4059_: *mut crate::leanh::LeanObject,
    mut v___y_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4063_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v_msg_4059_, v___y_4060_, v___y_4061_);
    return v___x_4063_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___boxed(
    mut v_00_u03b1_4064_: *mut crate::leanh::LeanObject,
    mut v_msg_4065_: *mut crate::leanh::LeanObject,
    mut v___y_4066_: *mut crate::leanh::LeanObject,
    mut v___y_4067_: *mut crate::leanh::LeanObject,
    mut v___y_4068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4069_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9(v_00_u03b1_4064_, v_msg_4065_, v___y_4066_, v___y_4067_);
    crate::leanh::lean_dec(v___y_4067_);
    crate::leanh::lean_dec_ref(v___y_4066_);
    return v_res_4069_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(
    mut v_00_u03b2_4070_: *mut crate::leanh::LeanObject,
    mut v_x_4071_: *mut crate::leanh::LeanObject,
    mut v_x_4072_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4073_: u8 = 0;
    v___x_4073_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___redArg(v_x_4071_, v_x_4072_);
    return v___x_4073_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b2_4074_: *mut crate::leanh::LeanObject,
    mut v_x_4075_: *mut crate::leanh::LeanObject,
    mut v_x_4076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4077_: u8 = 0;
    let mut v_r_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4077_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_4074_, v_x_4075_, v_x_4076_);
    crate::leanh::lean_dec_ref(v_x_4076_);
    crate::leanh::lean_dec_ref(v_x_4075_);
    v_r_4078_ = crate::leanh::lean_box((v_res_4077_) as usize);
    return v_r_4078_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(
    mut v_00_u03b2_4079_: *mut crate::leanh::LeanObject,
    mut v_a_4080_: *mut crate::leanh::LeanObject,
    mut v_x_4081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4082_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___redArg(v_a_4080_, v_x_4081_);
    return v___x_4082_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11___boxed(
    mut v_00_u03b2_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
    mut v_x_4085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4086_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__5_spec__11(v_00_u03b2_4083_, v_a_4084_, v_x_4085_);
    crate::leanh::lean_dec(v_x_4085_);
    crate::leanh::lean_dec(v_a_4084_);
    return v_res_4086_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(
    mut v_msgData_4087_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4088_: *mut crate::leanh::LeanObject,
    mut v___y_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4092_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___redArg(v_msgData_4087_, v_macroStack_4088_, v___y_4090_);
    return v___x_4092_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16___boxed(
    mut v_msgData_4093_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
    mut v___y_4096_: *mut crate::leanh::LeanObject,
    mut v___y_4097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4098_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9_spec__16(v_msgData_4093_, v_macroStack_4094_, v___y_4095_, v___y_4096_);
    crate::leanh::lean_dec(v___y_4096_);
    crate::leanh::lean_dec_ref(v___y_4095_);
    return v_res_4098_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(
    mut v_00_u03b2_4099_: *mut crate::leanh::LeanObject,
    mut v_x_4100_: *mut crate::leanh::LeanObject,
    mut v_x_4101_: usize,
    mut v_x_4102_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4103_: u8 = 0;
    v___x_4103_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___redArg(v_x_4100_, v_x_4101_, v_x_4102_);
    return v___x_4103_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12___boxed(
    mut v_00_u03b2_4104_: *mut crate::leanh::LeanObject,
    mut v_x_4105_: *mut crate::leanh::LeanObject,
    mut v_x_4106_: *mut crate::leanh::LeanObject,
    mut v_x_4107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_18713__boxed_4108_: usize = 0;
    let mut v_res_4109_: u8 = 0;
    let mut v_r_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_18713__boxed_4108_ = crate::leanh::lean_unbox_usize(v_x_4106_);
    crate::leanh::lean_dec(v_x_4106_);
    v_res_4109_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4104_, v_x_4105_, v_x_18713__boxed_4108_, v_x_4107_);
    crate::leanh::lean_dec_ref(v_x_4107_);
    crate::leanh::lean_dec_ref(v_x_4105_);
    v_r_4110_ = crate::leanh::lean_box((v_res_4109_) as usize);
    return v_r_4110_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(
    mut v_00_u03b2_4111_: *mut crate::leanh::LeanObject,
    mut v_keys_4112_: *mut crate::leanh::LeanObject,
    mut v_vals_4113_: *mut crate::leanh::LeanObject,
    mut v_heq_4114_: *mut crate::leanh::LeanObject,
    mut v_i_4115_: *mut crate::leanh::LeanObject,
    mut v_k_4116_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4117_: u8 = 0;
    v___x_4117_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___redArg(v_keys_4112_, v_i_4115_, v_k_4116_);
    return v___x_4117_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16___boxed(
    mut v_00_u03b2_4118_: *mut crate::leanh::LeanObject,
    mut v_keys_4119_: *mut crate::leanh::LeanObject,
    mut v_vals_4120_: *mut crate::leanh::LeanObject,
    mut v_heq_4121_: *mut crate::leanh::LeanObject,
    mut v_i_4122_: *mut crate::leanh::LeanObject,
    mut v_k_4123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4124_: u8 = 0;
    let mut v_r_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4124_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__1_spec__3_spec__8_spec__12_spec__16(v_00_u03b2_4118_, v_keys_4119_, v_vals_4120_, v_heq_4121_, v_i_4122_, v_k_4123_);
    crate::leanh::lean_dec_ref(v_k_4123_);
    crate::leanh::lean_dec_ref(v_vals_4120_);
    crate::leanh::lean_dec_ref(v_keys_4119_);
    v_r_4125_ = crate::leanh::lean_box((v_res_4124_) as usize);
    return v_r_4125_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_4140_;
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfOpaque(
    mut v_modifiers_4150_: *mut crate::leanh::LeanObject,
    mut v_stx_4151_: *mut crate::leanh::LeanObject,
    mut v_a_4152_: *mut crate::leanh::LeanObject,
    mut v_a_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4162_: u8 = 0;
    let mut v_val_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: u8 = 0;
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u8 = 0;
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4209_: u8 = 0;
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut v_a_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_4225_: u8 = 0;
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4243_: u8 = 0;
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut v_a_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4251_: u8 = 0;
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4255_: u8 = 0;
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: u8 = 0;
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4275_: u8 = 0;
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4279_: u8 = 0;
    let mut v_a_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4283_: u8 = 0;
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4287_: u8 = 0;
    let mut v_val_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4155_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4156_ = l_Lean_Syntax_getArg(v_stx_4151_, v___x_4155_);
                v___x_4157_ = l_Lean_Elab_expandDeclSig(v___x_4156_);
                crate::leanh::lean_dec(v___x_4156_);
                v_fst_4158_ = crate::leanh::lean_ctor_get(v___x_4157_, 0);
                v_snd_4159_ = crate::leanh::lean_ctor_get(v___x_4157_, 1);
                v_isSharedCheck_4289_ = (!crate::leanh::lean_is_exclusive(v___x_4157_)) as u8;
                if v_isSharedCheck_4289_ == 0 {
                    v___x_4161_ = v___x_4157_;
                    v_isShared_4162_ = v_isSharedCheck_4289_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4159_);
                    crate::leanh::lean_inc(v_fst_4158_);
                    crate::leanh::lean_dec(v___x_4157_);
                    v___x_4161_ = crate::leanh::lean_box(0);
                    v_isShared_4162_ = v_isSharedCheck_4289_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4222_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4223_ = l_Lean_Syntax_getArg(v_stx_4151_, v___x_4222_);
                v___x_4224_ = l_Lean_Syntax_getOptional_x3f(v___x_4223_);
                crate::leanh::lean_dec(v___x_4223_);
                if crate::leanh::lean_obj_tag(v___x_4224_) == 0 {
                    v_isUnsafe_4225_ = crate::leanh::lean_ctor_get_uint8(
                        v_modifiers_4150_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                    );
                    if v_isUnsafe_4225_ == 0 {
                        v___x_4226_ = l_Lean_Elab_Command_getRef___redArg(v_a_4152_);
                        if crate::leanh::lean_obj_tag(v___x_4226_) == 0 {
                            v_a_4227_ = crate::leanh::lean_ctor_get(v___x_4226_, 0);
                            crate::leanh::lean_inc(v_a_4227_);
                            crate::leanh::lean_dec_ref_known(v___x_4226_, 1);
                            v___x_4228_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_4152_);
                            if crate::leanh::lean_obj_tag(v___x_4228_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4228_, 1);
                                v_quotContext_x3f_4229_ = crate::leanh::lean_ctor_get(v_a_4152_, 5);
                                v___x_4230_ =
                                    l_Lean_SourceInfo_fromRef(v_a_4227_, v_isUnsafe_4225_);
                                crate::leanh::lean_dec(v_a_4227_);
                                if crate::leanh::lean_obj_tag(v_quotContext_x3f_4229_) == 0 {
                                    v___x_4239_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_4153_);
                                    crate::leanh::lean_dec_ref(v___x_4239_);
                                    state = 10;
                                    continue;
                                } else {
                                    state = 10;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4227_);
                                crate::leanh::lean_del_object(v___x_4161_);
                                crate::leanh::lean_dec(v_snd_4159_);
                                crate::leanh::lean_dec(v_fst_4158_);
                                crate::leanh::lean_dec(v_stx_4151_);
                                crate::leanh::lean_dec_ref(v_modifiers_4150_);
                                v_a_4240_ = crate::leanh::lean_ctor_get(v___x_4228_, 0);
                                v_isSharedCheck_4247_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4228_)) as u8;
                                if v_isSharedCheck_4247_ == 0 {
                                    v___x_4242_ = v___x_4228_;
                                    v_isShared_4243_ = v_isSharedCheck_4247_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4240_);
                                    crate::leanh::lean_dec(v___x_4228_);
                                    v___x_4242_ = crate::leanh::lean_box(0);
                                    v_isShared_4243_ = v_isSharedCheck_4247_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4161_);
                            crate::leanh::lean_dec(v_snd_4159_);
                            crate::leanh::lean_dec(v_fst_4158_);
                            crate::leanh::lean_dec(v_stx_4151_);
                            crate::leanh::lean_dec_ref(v_modifiers_4150_);
                            v_a_4248_ = crate::leanh::lean_ctor_get(v___x_4226_, 0);
                            v_isSharedCheck_4255_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4226_)) as u8;
                            if v_isSharedCheck_4255_ == 0 {
                                v___x_4250_ = v___x_4226_;
                                v_isShared_4251_ = v_isSharedCheck_4255_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4248_);
                                crate::leanh::lean_dec(v___x_4226_);
                                v___x_4250_ = crate::leanh::lean_box(0);
                                v_isShared_4251_ = v_isSharedCheck_4255_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        v___x_4256_ = l_Lean_Elab_Command_getRef___redArg(v_a_4152_);
                        if crate::leanh::lean_obj_tag(v___x_4256_) == 0 {
                            v_a_4257_ = crate::leanh::lean_ctor_get(v___x_4256_, 0);
                            crate::leanh::lean_inc(v_a_4257_);
                            crate::leanh::lean_dec_ref_known(v___x_4256_, 1);
                            v___x_4258_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_4152_);
                            if crate::leanh::lean_obj_tag(v___x_4258_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4258_, 1);
                                v_quotContext_x3f_4259_ = crate::leanh::lean_ctor_get(v_a_4152_, 5);
                                v___x_4260_ = 0;
                                v___x_4261_ = l_Lean_SourceInfo_fromRef(v_a_4257_, v___x_4260_);
                                crate::leanh::lean_dec(v_a_4257_);
                                if crate::leanh::lean_obj_tag(v_quotContext_x3f_4259_) == 0 {
                                    v___x_4271_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v_a_4153_);
                                    crate::leanh::lean_dec_ref(v___x_4271_);
                                    state = 15;
                                    continue;
                                } else {
                                    state = 15;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4257_);
                                crate::leanh::lean_del_object(v___x_4161_);
                                crate::leanh::lean_dec(v_snd_4159_);
                                crate::leanh::lean_dec(v_fst_4158_);
                                crate::leanh::lean_dec(v_stx_4151_);
                                crate::leanh::lean_dec_ref(v_modifiers_4150_);
                                v_a_4272_ = crate::leanh::lean_ctor_get(v___x_4258_, 0);
                                v_isSharedCheck_4279_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4258_)) as u8;
                                if v_isSharedCheck_4279_ == 0 {
                                    v___x_4274_ = v___x_4258_;
                                    v_isShared_4275_ = v_isSharedCheck_4279_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4272_);
                                    crate::leanh::lean_dec(v___x_4258_);
                                    v___x_4274_ = crate::leanh::lean_box(0);
                                    v_isShared_4275_ = v_isSharedCheck_4279_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4161_);
                            crate::leanh::lean_dec(v_snd_4159_);
                            crate::leanh::lean_dec(v_fst_4158_);
                            crate::leanh::lean_dec(v_stx_4151_);
                            crate::leanh::lean_dec_ref(v_modifiers_4150_);
                            v_a_4280_ = crate::leanh::lean_ctor_get(v___x_4256_, 0);
                            v_isSharedCheck_4287_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4256_)) as u8;
                            if v_isSharedCheck_4287_ == 0 {
                                v___x_4282_ = v___x_4256_;
                                v_isShared_4283_ = v_isSharedCheck_4287_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4280_);
                                crate::leanh::lean_dec(v___x_4256_);
                                v___x_4282_ = crate::leanh::lean_box(0);
                                v_isShared_4283_ = v_isSharedCheck_4287_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4161_);
                    v_val_4288_ = crate::leanh::lean_ctor_get(v___x_4224_, 0);
                    crate::leanh::lean_inc(v_val_4288_);
                    crate::leanh::lean_dec_ref_known(v___x_4224_, 1);
                    v_val_4164_ = v_val_4288_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_docString_x3f_4165_ = crate::leanh::lean_ctor_get(v_modifiers_4150_, 1);
                crate::leanh::lean_inc(v_docString_x3f_4165_);
                v___x_4166_ = 4;
                v___x_4167_ = l_Lean_Syntax_getArgs(v_stx_4151_);
                v___x_4168_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4169_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4170_ = l_Array_toSubarray___redArg(v___x_4167_, v___x_4169_, v___x_4168_);
                v___x_4171_ = l_Subarray_copy___redArg(v___x_4170_);
                v___x_4172_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_4173_ = crate::leanh::lean_box(2);
                v___x_4174_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4174_, 0, v___x_4173_);
                crate::leanh::lean_ctor_set(v___x_4174_, 1, v___x_4172_);
                crate::leanh::lean_ctor_set(v___x_4174_, 2, v___x_4171_);
                v___x_4175_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4176_ = l_Lean_Syntax_getArg(v_stx_4151_, v___x_4175_);
                v___x_4177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4177_, 0, v_snd_4159_);
                v___x_4178_ = crate::leanh::lean_box(0);
                v___x_4179_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4179_, 0, v_stx_4151_);
                crate::leanh::lean_ctor_set(v___x_4179_, 1, v___x_4174_);
                crate::leanh::lean_ctor_set(v___x_4179_, 2, v_modifiers_4150_);
                crate::leanh::lean_ctor_set(v___x_4179_, 3, v___x_4176_);
                crate::leanh::lean_ctor_set(v___x_4179_, 4, v_fst_4158_);
                crate::leanh::lean_ctor_set(v___x_4179_, 5, v___x_4177_);
                crate::leanh::lean_ctor_set(v___x_4179_, 6, v_val_4164_);
                crate::leanh::lean_ctor_set(v___x_4179_, 7, v_docString_x3f_4165_);
                crate::leanh::lean_ctor_set(v___x_4179_, 8, v___x_4178_);
                crate::leanh::lean_ctor_set(v___x_4179_, 9, v___x_4178_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4179_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    v___x_4166_,
                );
                v___x_4180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4180_, 0, v___x_4179_);
                return v___x_4180_;
            }
            3 => {
                v___x_4184_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__1;
                v___x_4185_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__2;
                crate::leanh::lean_inc(v___y_4183_);
                if v_isShared_4162_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4161_, 2);
                    crate::leanh::lean_ctor_set(v___x_4161_, 1, v___x_4185_);
                    crate::leanh::lean_ctor_set(v___x_4161_, 0, v___y_4183_);
                    v___x_4187_ = v___x_4161_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4194_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___y_4183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4194_, 1, v___x_4185_);
                    v___x_4187_ = v_reuseFailAlloc_4194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4188_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__5;
                v___x_4189_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_4190_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once),
                    _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6,
                );
                crate::leanh::lean_inc_n(v___y_4183_, 2);
                v___x_4191_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4191_, 0, v___y_4183_);
                crate::leanh::lean_ctor_set(v___x_4191_, 1, v___x_4189_);
                crate::leanh::lean_ctor_set(v___x_4191_, 2, v___x_4190_);
                crate::leanh::lean_inc_ref_n(v___x_4191_, 2);
                v___x_4192_ =
                    l_Lean_Syntax_node2(v___y_4183_, v___x_4188_, v___x_4191_, v___x_4191_);
                v___x_4193_ = l_Lean_Syntax_node4(
                    v___y_4183_,
                    v___x_4184_,
                    v___x_4187_,
                    v___y_4182_,
                    v___x_4192_,
                    v___x_4191_,
                );
                v_val_4164_ = v___x_4193_;
                state = 2;
                continue;
            }
            5 => {
                v___x_4199_ = l_Lean_Elab_Command_getRef___redArg(v___y_4197_);
                if crate::leanh::lean_obj_tag(v___x_4199_) == 0 {
                    v_a_4200_ = crate::leanh::lean_ctor_get(v___x_4199_, 0);
                    crate::leanh::lean_inc(v_a_4200_);
                    crate::leanh::lean_dec_ref_known(v___x_4199_, 1);
                    v___x_4201_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_4197_);
                    if crate::leanh::lean_obj_tag(v___x_4201_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4201_, 1);
                        v_quotContext_x3f_4202_ = crate::leanh::lean_ctor_get(v___y_4197_, 5);
                        v___x_4203_ = 0;
                        v___x_4204_ = l_Lean_SourceInfo_fromRef(v_a_4200_, v___x_4203_);
                        crate::leanh::lean_dec(v_a_4200_);
                        if crate::leanh::lean_obj_tag(v_quotContext_x3f_4202_) == 0 {
                            v___x_4205_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__2___redArg(v___y_4198_);
                            crate::leanh::lean_dec_ref(v___x_4205_);
                            v___y_4182_ = v_val_4196_;
                            v___y_4183_ = v___x_4204_;
                            state = 3;
                            continue;
                        } else {
                            v___y_4182_ = v_val_4196_;
                            v___y_4183_ = v___x_4204_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4200_);
                        crate::leanh::lean_dec(v_val_4196_);
                        crate::leanh::lean_del_object(v___x_4161_);
                        crate::leanh::lean_dec(v_snd_4159_);
                        crate::leanh::lean_dec(v_fst_4158_);
                        crate::leanh::lean_dec(v_stx_4151_);
                        crate::leanh::lean_dec_ref(v_modifiers_4150_);
                        v_a_4206_ = crate::leanh::lean_ctor_get(v___x_4201_, 0);
                        v_isSharedCheck_4213_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4201_)) as u8;
                        if v_isSharedCheck_4213_ == 0 {
                            v___x_4208_ = v___x_4201_;
                            v_isShared_4209_ = v_isSharedCheck_4213_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4206_);
                            crate::leanh::lean_dec(v___x_4201_);
                            v___x_4208_ = crate::leanh::lean_box(0);
                            v_isShared_4209_ = v_isSharedCheck_4213_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_val_4196_);
                    crate::leanh::lean_del_object(v___x_4161_);
                    crate::leanh::lean_dec(v_snd_4159_);
                    crate::leanh::lean_dec(v_fst_4158_);
                    crate::leanh::lean_dec(v_stx_4151_);
                    crate::leanh::lean_dec_ref(v_modifiers_4150_);
                    v_a_4214_ = crate::leanh::lean_ctor_get(v___x_4199_, 0);
                    v_isSharedCheck_4221_ = (!crate::leanh::lean_is_exclusive(v___x_4199_)) as u8;
                    if v_isSharedCheck_4221_ == 0 {
                        v___x_4216_ = v___x_4199_;
                        v_isShared_4217_ = v_isSharedCheck_4221_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4214_);
                        crate::leanh::lean_dec(v___x_4199_);
                        v___x_4216_ = crate::leanh::lean_box(0);
                        v_isShared_4217_ = v_isSharedCheck_4221_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4209_ == 0 {
                    v___x_4211_ = v___x_4208_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
                    v___x_4211_ = v_reuseFailAlloc_4212_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4211_;
            }
            8 => {
                if v_isShared_4217_ == 0 {
                    v___x_4219_ = v___x_4216_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
                    v___x_4219_ = v_reuseFailAlloc_4220_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4219_;
            }
            10 => {
                v___x_4232_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9;
                v___x_4233_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10;
                crate::leanh::lean_inc_n(v___x_4230_, 2);
                v___x_4234_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4234_, 0, v___x_4230_);
                crate::leanh::lean_ctor_set(v___x_4234_, 1, v___x_4233_);
                v___x_4235_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_4236_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6_once),
                    _init_l_Lean_Elab_Command_mkDefViewOfOpaque___closed__6,
                );
                v___x_4237_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4237_, 0, v___x_4230_);
                crate::leanh::lean_ctor_set(v___x_4237_, 1, v___x_4235_);
                crate::leanh::lean_ctor_set(v___x_4237_, 2, v___x_4236_);
                v___x_4238_ =
                    l_Lean_Syntax_node2(v___x_4230_, v___x_4232_, v___x_4234_, v___x_4237_);
                v_val_4196_ = v___x_4238_;
                v___y_4197_ = v_a_4152_;
                v___y_4198_ = v_a_4153_;
                state = 5;
                continue;
            }
            11 => {
                if v_isShared_4243_ == 0 {
                    v___x_4245_ = v___x_4242_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
                    v___x_4245_ = v_reuseFailAlloc_4246_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4245_;
            }
            13 => {
                if v_isShared_4251_ == 0 {
                    v___x_4253_ = v___x_4250_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
                    v___x_4253_ = v_reuseFailAlloc_4254_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4253_;
            }
            15 => {
                v___x_4263_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__9;
                v___x_4264_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__10;
                crate::leanh::lean_inc_n(v___x_4261_, 3);
                v___x_4265_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4265_, 0, v___x_4261_);
                crate::leanh::lean_ctor_set(v___x_4265_, 1, v___x_4264_);
                v___x_4266_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
                v___x_4267_ = l_Lean_Elab_Command_mkDefViewOfOpaque___closed__11;
                v___x_4268_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4268_, 0, v___x_4261_);
                crate::leanh::lean_ctor_set(v___x_4268_, 1, v___x_4267_);
                v___x_4269_ = l_Lean_Syntax_node1(v___x_4261_, v___x_4266_, v___x_4268_);
                v___x_4270_ =
                    l_Lean_Syntax_node2(v___x_4261_, v___x_4263_, v___x_4265_, v___x_4269_);
                v_val_4196_ = v___x_4270_;
                v___y_4197_ = v_a_4152_;
                v___y_4198_ = v_a_4153_;
                state = 5;
                continue;
            }
            16 => {
                if v_isShared_4275_ == 0 {
                    v___x_4277_ = v___x_4274_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4278_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
                    v___x_4277_ = v_reuseFailAlloc_4278_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4277_;
            }
            18 => {
                if v_isShared_4283_ == 0 {
                    v___x_4285_ = v___x_4282_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4286_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
                    v___x_4285_ = v_reuseFailAlloc_4286_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfOpaque___boxed(
    mut v_modifiers_4290_: *mut crate::leanh::LeanObject,
    mut v_stx_4291_: *mut crate::leanh::LeanObject,
    mut v_a_4292_: *mut crate::leanh::LeanObject,
    mut v_a_4293_: *mut crate::leanh::LeanObject,
    mut v_a_4294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4295_ =
        l_Lean_Elab_Command_mkDefViewOfOpaque(v_modifiers_4290_, v_stx_4291_, v_a_4292_, v_a_4293_);
    crate::leanh::lean_dec(v_a_4293_);
    crate::leanh::lean_dec_ref(v_a_4292_);
    return v_res_4295_;
}
pub unsafe fn l_Lean_Elab_Command_mkDefViewOfExample(
    mut v_modifiers_4308_: *mut crate::leanh::LeanObject,
    mut v_stx_4309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: u8 = 0;
    let mut v_id_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: u8 = 0;
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4310_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4311_ = l_Lean_Syntax_getArg(v_stx_4309_, v___x_4310_);
    v___x_4312_ = l_Lean_Elab_expandOptDeclSig(v___x_4311_);
    crate::leanh::lean_dec(v___x_4311_);
    v_fst_4313_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
    crate::leanh::lean_inc(v_fst_4313_);
    v_snd_4314_ = crate::leanh::lean_ctor_get(v___x_4312_, 1);
    crate::leanh::lean_inc(v_snd_4314_);
    crate::leanh::lean_dec_ref(v___x_4312_);
    v___x_4315_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4316_ = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__7;
    v___x_4317_ = crate::leanh::lean_box(2);
    v___x_4318_ = l_Lean_Elab_Command_mkDefViewOfExample___closed__0;
    v_docString_x3f_4319_ = crate::leanh::lean_ctor_get(v_modifiers_4308_, 1);
    crate::leanh::lean_inc(v_docString_x3f_4319_);
    v___x_4320_ = l_Lean_Syntax_getArg(v_stx_4309_, v___x_4315_);
    v___x_4321_ = l_Lean_Elab_Command_mkDefViewOfExample___closed__2;
    v___x_4322_ = 1;
    v_id_4323_ = l_Lean_mkIdentFrom(v___x_4320_, v___x_4321_, v___x_4322_);
    crate::leanh::lean_dec(v___x_4320_);
    v___x_4324_ = l_Lean_Elab_Command_mkDefViewOfExample___closed__3;
    v___x_4325_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_4326_ = lean_mk_empty_array_with_capacity(v___x_4325_);
    v___x_4327_ = lean_array_push(v___x_4326_, v_id_4323_);
    v___x_4328_ = lean_array_push(v___x_4327_, v___x_4318_);
    v___x_4329_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4329_, 0, v___x_4317_);
    crate::leanh::lean_ctor_set(v___x_4329_, 1, v___x_4324_);
    crate::leanh::lean_ctor_set(v___x_4329_, 2, v___x_4328_);
    v___x_4330_ = 3;
    v___x_4331_ = l_Lean_Syntax_getArgs(v_stx_4309_);
    v___x_4332_ = l_Array_toSubarray___redArg(v___x_4331_, v___x_4315_, v___x_4325_);
    v___x_4333_ = l_Subarray_copy___redArg(v___x_4332_);
    v___x_4334_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4334_, 0, v___x_4317_);
    crate::leanh::lean_ctor_set(v___x_4334_, 1, v___x_4316_);
    crate::leanh::lean_ctor_set(v___x_4334_, 2, v___x_4333_);
    v___x_4335_ = l_Lean_Syntax_getArg(v_stx_4309_, v___x_4325_);
    v___x_4336_ = crate::leanh::lean_box(0);
    v___x_4337_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4337_, 0, v_stx_4309_);
    crate::leanh::lean_ctor_set(v___x_4337_, 1, v___x_4334_);
    crate::leanh::lean_ctor_set(v___x_4337_, 2, v_modifiers_4308_);
    crate::leanh::lean_ctor_set(v___x_4337_, 3, v___x_4329_);
    crate::leanh::lean_ctor_set(v___x_4337_, 4, v_fst_4313_);
    crate::leanh::lean_ctor_set(v___x_4337_, 5, v_snd_4314_);
    crate::leanh::lean_ctor_set(v___x_4337_, 6, v___x_4335_);
    crate::leanh::lean_ctor_set(v___x_4337_, 7, v_docString_x3f_4319_);
    crate::leanh::lean_ctor_set(v___x_4337_, 8, v___x_4336_);
    crate::leanh::lean_ctor_set(v___x_4337_, 9, v___x_4336_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4337_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
        v___x_4330_,
    );
    return v___x_4337_;
}
pub unsafe fn l_Lean_Elab_Command_isDefLike(mut v_stx_4373_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_declKind_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4376_: u8 = 0;
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: u8 = 0;
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: u8 = 0;
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: u8 = 0;
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: u8 = 0;
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declKind_4374_ = l_Lean_Syntax_getKind(v_stx_4373_);
                v___x_4385_ = l_Lean_Elab_Command_isDefLike___closed__8;
                v___x_4386_ = lean_name_eq(v_declKind_4374_, v___x_4385_);
                if v___x_4386_ == 0 {
                    v___x_4387_ = l_Lean_Elab_Command_isDefLike___closed__10;
                    v___x_4388_ = lean_name_eq(v_declKind_4374_, v___x_4387_);
                    v___y_4376_ = v___x_4388_;
                    state = 1;
                    continue;
                } else {
                    v___y_4376_ = v___x_4386_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4376_ == 0 {
                    v___x_4377_ = l_Lean_Elab_Command_isDefLike___closed__1;
                    v___x_4378_ = lean_name_eq(v_declKind_4374_, v___x_4377_);
                    if v___x_4378_ == 0 {
                        v___x_4379_ = l_Lean_Elab_Command_isDefLike___closed__3;
                        v___x_4380_ = lean_name_eq(v_declKind_4374_, v___x_4379_);
                        if v___x_4380_ == 0 {
                            v___x_4381_ = l_Lean_Elab_Command_isDefLike___closed__4;
                            v___x_4382_ = lean_name_eq(v_declKind_4374_, v___x_4381_);
                            if v___x_4382_ == 0 {
                                v___x_4383_ = l_Lean_Elab_Command_isDefLike___closed__6;
                                v___x_4384_ = lean_name_eq(v_declKind_4374_, v___x_4383_);
                                crate::leanh::lean_dec(v_declKind_4374_);
                                return v___x_4384_;
                            } else {
                                crate::leanh::lean_dec(v_declKind_4374_);
                                return v___x_4382_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_declKind_4374_);
                            return v___x_4380_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declKind_4374_);
                        return v___x_4378_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declKind_4374_);
                    return v___y_4376_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_isDefLike___boxed(
    mut v_stx_4389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4390_: u8 = 0;
    let mut v_r_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4390_ = l_Lean_Elab_Command_isDefLike(v_stx_4389_);
    v_r_4391_ = crate::leanh::lean_box((v_res_4390_) as usize);
    return v_r_4391_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkDefView___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4393_ = l_Lean_Elab_Command_mkDefView___closed__0;
    v___x_4394_ = l_Lean_stringToMessageData(v___x_4393_);
    return v___x_4394_;
}
pub unsafe fn l_Lean_Elab_Command_mkDefView(
    mut v_modifiers_4395_: *mut crate::leanh::LeanObject,
    mut v_stx_4396_: *mut crate::leanh::LeanObject,
    mut v_a_4397_: *mut crate::leanh::LeanObject,
    mut v_a_4398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v_stx_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visibility_4407_: u8 = 0;
    let mut v_isProtected_4408_: u8 = 0;
    let mut v_computeKind_4409_: u8 = 0;
    let mut v_recKind_4410_: u8 = 0;
    let mut v_isUnsafe_4411_: u8 = 0;
    let mut v_attrs_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declKind_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: u8 = 0;
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: u8 = 0;
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: u8 = 0;
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: u8 = 0;
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: u8 = 0;
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4449_: u8 = 0;
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: u8 = 0;
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: u8 = 0;
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v___x_4457_: u8 = 0;
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4461_: u8 = 0;
    let mut v_unused_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v___x_4466_: u8 = 0;
    let mut v_isMeta_4467_: u8 = 0;
    let mut v_isSharedCheck_4468_: u8 = 0;
    let mut v_a_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4472_: u8 = 0;
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4400_ = l_Lean_Elab_Command_getScope___redArg(v_a_4398_);
                if crate::leanh::lean_obj_tag(v___x_4400_) == 0 {
                    v_a_4401_ = crate::leanh::lean_ctor_get(v___x_4400_, 0);
                    v_isSharedCheck_4468_ = (!crate::leanh::lean_is_exclusive(v___x_4400_)) as u8;
                    if v_isSharedCheck_4468_ == 0 {
                        v___x_4403_ = v___x_4400_;
                        v_isShared_4404_ = v_isSharedCheck_4468_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4401_);
                        crate::leanh::lean_dec(v___x_4400_);
                        v___x_4403_ = crate::leanh::lean_box(0);
                        v_isShared_4404_ = v_isSharedCheck_4468_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_4396_);
                    crate::leanh::lean_dec_ref(v_modifiers_4395_);
                    v_a_4469_ = crate::leanh::lean_ctor_get(v___x_4400_, 0);
                    v_isSharedCheck_4476_ = (!crate::leanh::lean_is_exclusive(v___x_4400_)) as u8;
                    if v_isSharedCheck_4476_ == 0 {
                        v___x_4471_ = v___x_4400_;
                        v_isShared_4472_ = v_isSharedCheck_4476_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4469_);
                        crate::leanh::lean_dec(v___x_4400_);
                        v___x_4471_ = crate::leanh::lean_box(0);
                        v_isShared_4472_ = v_isSharedCheck_4476_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_stx_4405_ = crate::leanh::lean_ctor_get(v_modifiers_4395_, 0);
                v_docString_x3f_4406_ = crate::leanh::lean_ctor_get(v_modifiers_4395_, 1);
                v_visibility_4407_ = crate::leanh::lean_ctor_get_uint8(
                    v_modifiers_4395_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isProtected_4408_ = crate::leanh::lean_ctor_get_uint8(
                    v_modifiers_4395_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_computeKind_4409_ = crate::leanh::lean_ctor_get_uint8(
                    v_modifiers_4395_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_recKind_4410_ = crate::leanh::lean_ctor_get_uint8(
                    v_modifiers_4395_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                );
                v_isUnsafe_4411_ = crate::leanh::lean_ctor_get_uint8(
                    v_modifiers_4395_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                );
                v_attrs_4412_ = crate::leanh::lean_ctor_get(v_modifiers_4395_, 2);
                crate::leanh::lean_inc(v_stx_4396_);
                v_declKind_4413_ = l_Lean_Syntax_getKind(v_stx_4396_);
                v___x_4465_ = 0;
                v___x_4466_ = l_Lean_Elab_instBEqComputeKind_beq(v_computeKind_4409_, v___x_4465_);
                if v___x_4466_ == 0 {
                    crate::leanh::lean_dec(v_a_4401_);
                    v___y_4449_ = v___x_4466_;
                    state = 7;
                    continue;
                } else {
                    v_isMeta_4467_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4401_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10 + 2) as u32,
                    );
                    crate::leanh::lean_dec(v_a_4401_);
                    v___y_4449_ = v_isMeta_4467_;
                    state = 7;
                    continue;
                }
            }
            2 => {
                v___x_4416_ = l_Lean_Elab_Command_isDefLike___closed__8;
                v___x_4417_ = lean_name_eq(v_declKind_4413_, v___x_4416_);
                if v___x_4417_ == 0 {
                    v___x_4418_ = l_Lean_Elab_Command_isDefLike___closed__10;
                    v___x_4419_ = lean_name_eq(v_declKind_4413_, v___x_4418_);
                    if v___x_4419_ == 0 {
                        v___x_4420_ = l_Lean_Elab_Command_isDefLike___closed__1;
                        v___x_4421_ = lean_name_eq(v_declKind_4413_, v___x_4420_);
                        if v___x_4421_ == 0 {
                            v___x_4422_ = l_Lean_Elab_Command_isDefLike___closed__3;
                            v___x_4423_ = lean_name_eq(v_declKind_4413_, v___x_4422_);
                            if v___x_4423_ == 0 {
                                v___x_4424_ = l_Lean_Elab_Command_isDefLike___closed__4;
                                v___x_4425_ = lean_name_eq(v_declKind_4413_, v___x_4424_);
                                if v___x_4425_ == 0 {
                                    v___x_4426_ = l_Lean_Elab_Command_isDefLike___closed__6;
                                    v___x_4427_ = lean_name_eq(v_declKind_4413_, v___x_4426_);
                                    crate::leanh::lean_dec(v_declKind_4413_);
                                    if v___x_4427_ == 0 {
                                        crate::leanh::lean_dec_ref(v___y_4415_);
                                        crate::leanh::lean_del_object(v___x_4403_);
                                        crate::leanh::lean_dec(v_stx_4396_);
                                        v___x_4428_ = crate::leanh::lean_obj_once(
                                            core::ptr::addr_of_mut!(
                                                l_Lean_Elab_Command_mkDefView___closed__1
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Lean_Elab_Command_mkDefView___closed__1_once
                                            ),
                                            _init_l_Lean_Elab_Command_mkDefView___closed__1,
                                        );
                                        v___x_4429_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_mkDefViewOfInstance_spec__0_spec__4_spec__9___redArg(v___x_4428_, v_a_4397_, v_a_4398_);
                                        return v___x_4429_;
                                    } else {
                                        v___x_4430_ = l_Lean_Elab_Command_mkDefViewOfExample(
                                            v___y_4415_,
                                            v_stx_4396_,
                                        );
                                        if v_isShared_4404_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_4403_,
                                                0,
                                                v___x_4430_,
                                            );
                                            v___x_4432_ = v___x_4403_;
                                            state = 3;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_4433_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4433_,
                                                0,
                                                v___x_4430_,
                                            );
                                            v___x_4432_ = v_reuseFailAlloc_4433_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_declKind_4413_);
                                    crate::leanh::lean_del_object(v___x_4403_);
                                    v___x_4434_ = l_Lean_Elab_Command_mkDefViewOfInstance(
                                        v___y_4415_,
                                        v_stx_4396_,
                                        v_a_4397_,
                                        v_a_4398_,
                                    );
                                    return v___x_4434_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_declKind_4413_);
                                crate::leanh::lean_del_object(v___x_4403_);
                                v___x_4435_ = l_Lean_Elab_Command_mkDefViewOfOpaque(
                                    v___y_4415_,
                                    v_stx_4396_,
                                    v_a_4397_,
                                    v_a_4398_,
                                );
                                return v___x_4435_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_declKind_4413_);
                            v___x_4436_ =
                                l_Lean_Elab_Command_mkDefViewOfTheorem(v___y_4415_, v_stx_4396_);
                            if v_isShared_4404_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4403_, 0, v___x_4436_);
                                v___x_4438_ = v___x_4403_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_4439_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
                                v___x_4438_ = v_reuseFailAlloc_4439_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_declKind_4413_);
                        v___x_4440_ = l_Lean_Elab_Command_mkDefViewOfDef(v___y_4415_, v_stx_4396_);
                        if v_isShared_4404_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4403_, 0, v___x_4440_);
                            v___x_4442_ = v___x_4403_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4443_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
                            v___x_4442_ = v_reuseFailAlloc_4443_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declKind_4413_);
                    v___x_4444_ = l_Lean_Elab_Command_mkDefViewOfAbbrev(v___y_4415_, v_stx_4396_);
                    if v_isShared_4404_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4403_, 0, v___x_4444_);
                        v___x_4446_ = v___x_4403_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4444_);
                        v___x_4446_ = v_reuseFailAlloc_4447_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4432_;
            }
            4 => {
                return v___x_4438_;
            }
            5 => {
                return v___x_4442_;
            }
            6 => {
                return v___x_4446_;
            }
            7 => {
                if v___y_4449_ == 0 {
                    v___y_4415_ = v_modifiers_4395_;
                    state = 2;
                    continue;
                } else {
                    v___x_4450_ = l_Lean_Elab_Command_isDefLike___closed__1;
                    v___x_4451_ = lean_name_eq(v_declKind_4413_, v___x_4450_);
                    if v___x_4451_ == 0 {
                        v___x_4452_ = l_Lean_Elab_Command_isDefLike___closed__6;
                        v___x_4453_ = lean_name_eq(v_declKind_4413_, v___x_4452_);
                        if v___x_4453_ == 0 {
                            crate::leanh::lean_inc_ref(v_attrs_4412_);
                            crate::leanh::lean_inc(v_docString_x3f_4406_);
                            crate::leanh::lean_inc(v_stx_4405_);
                            v_isSharedCheck_4461_ =
                                (!crate::leanh::lean_is_exclusive(v_modifiers_4395_)) as u8;
                            if v_isSharedCheck_4461_ == 0 {
                                v_unused_4462_ = crate::leanh::lean_ctor_get(v_modifiers_4395_, 2);
                                crate::leanh::lean_dec(v_unused_4462_);
                                v_unused_4463_ = crate::leanh::lean_ctor_get(v_modifiers_4395_, 1);
                                crate::leanh::lean_dec(v_unused_4463_);
                                v_unused_4464_ = crate::leanh::lean_ctor_get(v_modifiers_4395_, 0);
                                crate::leanh::lean_dec(v_unused_4464_);
                                v___x_4455_ = v_modifiers_4395_;
                                v_isShared_4456_ = v_isSharedCheck_4461_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_modifiers_4395_);
                                v___x_4455_ = crate::leanh::lean_box(0);
                                v_isShared_4456_ = v_isSharedCheck_4461_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___y_4415_ = v_modifiers_4395_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_4415_ = v_modifiers_4395_;
                        state = 2;
                        continue;
                    }
                }
            }
            8 => {
                v___x_4457_ = 1;
                if v_isShared_4456_ == 0 {
                    v___x_4459_ = v___x_4455_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4460_ = crate::leanh::lean_alloc_ctor(0, 3, (5) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_stx_4405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4460_, 1, v_docString_x3f_4406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4460_, 2, v_attrs_4412_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4460_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_visibility_4407_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4460_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_isProtected_4408_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4460_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                        v_recKind_4410_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4460_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                        v_isUnsafe_4411_,
                    );
                    v___x_4459_ = v_reuseFailAlloc_4460_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4459_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                    v___x_4457_,
                );
                v___y_4415_ = v___x_4459_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_4472_ == 0 {
                    v___x_4474_ = v___x_4471_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
                    v___x_4474_ = v_reuseFailAlloc_4475_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkDefView___boxed(
    mut v_modifiers_4477_: *mut crate::leanh::LeanObject,
    mut v_stx_4478_: *mut crate::leanh::LeanObject,
    mut v_a_4479_: *mut crate::leanh::LeanObject,
    mut v_a_4480_: *mut crate::leanh::LeanObject,
    mut v_a_4481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4482_ =
        l_Lean_Elab_Command_mkDefView(v_modifiers_4477_, v_stx_4478_, v_a_4479_, v_a_4480_);
    crate::leanh::lean_dec(v_a_4480_);
    crate::leanh::lean_dec_ref(v_a_4479_);
    return v_res_4482_;
}
pub unsafe fn l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: u8 = 0;
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4544_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_;
    v___x_4545_ = 0;
    v___x_4546_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_;
    v___x_4547_ = l_Lean_registerTraceClass(v___x_4544_, v___x_4545_, v___x_4546_);
    return v___x_4547_;
}
pub unsafe fn l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2____boxed(
    mut v_a_4548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4549_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
    return v_res_4549_;
}
pub unsafe fn _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4550_ = crate::leanh::lean_unsigned_to_nat(2390142386);
    v___x_4551_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_;
    v___x_4552_ = l_Lean_Name_num___override(v___x_4551_, v___x_4550_);
    return v___x_4552_;
}
pub unsafe fn _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4553_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_;
    v___x_4554_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
    v___x_4555_ = l_Lean_Name_str___override(v___x_4554_, v___x_4553_);
    return v___x_4555_;
}
pub unsafe fn _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4556_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_;
    v___x_4557_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
    v___x_4558_ = l_Lean_Name_str___override(v___x_4557_, v___x_4556_);
    return v___x_4558_;
}
pub unsafe fn _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4559_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_4560_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
    v___x_4561_ = l_Lean_Name_num___override(v___x_4560_, v___x_4559_);
    return v___x_4561_;
}
pub unsafe fn l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4563_ = l_Lean_Elab_Command_mkDefViewOfInstance___closed__6;
    v___x_4564_ = 0;
    v___x_4565_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_);
    v___x_4566_ = l_Lean_registerTraceClass(v___x_4563_, v___x_4564_, v___x_4565_);
    return v___x_4566_;
}
pub unsafe fn l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2____boxed(
    mut v_a_4567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4568_ = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
    return v_res_4568_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DefView(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_DeclNameGen(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Elab_instInhabitedDefKind_default = _init_l_Lean_Elab_instInhabitedDefKind_default();
    l_Lean_Elab_instInhabitedDefKind = _init_l_Lean_Elab_instInhabitedDefKind();
    l_Lean_Elab_instInhabitedDefViewElabHeaderData_default =
        _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedDefViewElabHeaderData_default);
    l_Lean_Elab_instInhabitedDefViewElabHeaderData =
        _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedDefViewElabHeaderData);
    l_Lean_Elab_instInhabitedDefView_default = _init_l_Lean_Elab_instInhabitedDefView_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedDefView_default);
    l_Lean_Elab_instInhabitedDefView = _init_l_Lean_Elab_instInhabitedDefView();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedDefView);
    res = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_1745620379____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_DefView_2390142386____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DefView(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_DefView(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_DeclNameGen(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_DeclUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DefView(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DefView(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_DefView(builtin);
}

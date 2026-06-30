// Lean compiler output
// Module: Lean.Linter.Deprecated
// Imports: Lean.Meta.Basic Lean.Linter.Init Lean.Elab.InfoTree.Main Lean.ExtraModUses Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_size, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_lt,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_uint64_lor,
    lean_uint64_of_nat, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getString};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr2, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_replaceRef, l_List_get___redArg, l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_ParametricAttribute_getParam_x3f___redArg, l_Lean_ParametricAttribute_setParam___redArg,
    l_Lean_registerParametricAttribute___redArg,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::{
    l_Lean_Name_componentsRev, l_Lean_Name_getPrefix, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    initialize_Lean_Elab_InfoTree_Main, l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo,
    runtime_initialize_Lean_Elab_InfoTree_Main,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_PersistentEnvExtension_addEntry___redArg, l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::ExtraModUses::{
    initialize_Lean_ExtraModUses, l___private_Lean_ExtraModUses_0__Lean_extraModUses,
    l_Lean_indirectModUseExt, l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
    runtime_initialize_Lean_ExtraModUses,
};
use crate::r#gen::Lean::Linter::Init::{
    initialize_Lean_Linter_Init, l_Lean_Linter_getLinterValue, l_Lean_Linter_linterSetsExt,
    runtime_initialize_Lean_Linter_Init,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_nil,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_indentExpr,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_isExprDefEqGuarded,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Modifiers::l_Lean_isProtected;
use crate::r#gen::Lean::MonadEnv::l_Lean_setEnv___redArg;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,5701751079888345786 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13546154976408593379 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [105, 102, 32, 116, 114, 117, 101, 44, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 100, 101, 112, 114, 101, 99, 97, 116, 105, 111, 110, 32, 119, 97, 114, 110, 105, 110, 103, 115, 0]};
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8071394701935581384 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6326339448686113589 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14679817356290926072 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Linter_linter_deprecated: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Linter_instInhabitedDeprecationEntry_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Linter_instInhabitedDeprecationEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_instInhabitedDeprecationEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__6_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__6_value) as *mut leanh::LeanObject,7870113334857981723 as *mut leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__8_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__10_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__13_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__13_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__14_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__16_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__16_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__18_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__18_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__20_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__21_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__22_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__23_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__23_value) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__3_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanStringObject<134> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 134, m_capacity: 134, m_length: 133, m_data: [96, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 104, 111, 117, 108, 100, 32, 115, 112, 101, 99, 105, 102, 121, 32, 116, 104, 101, 32, 100, 97, 116, 101, 32, 111, 114, 32, 108, 105, 98, 114, 97, 114, 121, 32, 118, 101, 114, 115, 105, 111, 110, 32, 97, 116, 32, 119, 104, 105, 99, 104, 32, 116, 104, 101, 32, 100, 101, 112, 114, 101, 99, 97, 116, 105, 111, 110, 32, 119, 97, 115, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 100, 44, 32, 117, 115, 105, 110, 103, 32, 96, 40, 115, 105, 110, 99, 101, 32, 58, 61, 32, 34, 46, 46, 46, 34, 41, 96, 0]};
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanStringObject<83> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [96, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 104, 111, 117, 108, 100, 32, 115, 112, 101, 99, 105, 102, 121, 32, 101, 105, 116, 104, 101, 114, 32, 97, 32, 110, 101, 119, 32, 110, 97, 109, 101, 32, 111, 114, 32, 97, 32, 100, 101, 112, 114, 101, 99, 97, 116, 105, 111, 110, 32, 109, 101, 115, 115, 97, 103, 101, 0]};
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 91, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8071394701935581384 as *mut leanh::LeanObject] };
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11717111273439622741 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanClosureObject<2> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10099171310552725070 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanStringObject<31> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [109, 97, 114, 107, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 97, 115, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 8) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Linter_deprecatedAttr: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MessageData_isDeprecationWarning___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_MessageData_isDeprecationWarning___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_MessageData_isDeprecationWarning___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_isDeprecationWarning___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Linter_checkDeprecated___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [96, 0],
    };
static mut l_Lean_Linter_checkDeprecated___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__2_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            96, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116,
            101, 100, 0,
        ],
    };
static mut l_Lean_Linter_checkDeprecated___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__4_value: leanh::LeanStringObject<86> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 86,
        m_capacity: 86,
        m_length: 85,
        m_data: [
            84, 104, 101, 32, 117, 112, 100, 97, 116, 101, 100, 32, 99, 111, 110, 115, 116, 97,
            110, 116, 32, 105, 115, 32, 105, 110, 32, 97, 32, 100, 105, 102, 102, 101, 114, 101,
            110, 116, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 46, 32, 68, 111, 116, 32, 110,
            111, 116, 97, 116, 105, 111, 110, 32, 109, 97, 121, 32, 110, 101, 101, 100, 32, 116,
            111, 32, 98, 101, 32, 99, 104, 97, 110, 103, 101, 100, 0,
        ],
    };
static mut l_Lean_Linter_checkDeprecated___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__6_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Linter_checkDeprecated___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__8_value: leanh::LeanStringObject<8> =
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
        m_data: [58, 32, 85, 115, 101, 32, 96, 0],
    };
static mut l_Lean_Linter_checkDeprecated___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__10_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [96, 32, 105, 110, 115, 116, 101, 97, 100, 0],
    };
static mut l_Lean_Linter_checkDeprecated___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__12_value: leanh::LeanStringObject<58> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 58,
        m_capacity: 58,
        m_length: 57,
        m_data: [
            96, 32, 105, 115, 32, 112, 114, 111, 116, 101, 99, 116, 101, 100, 46, 32, 82, 101, 102,
            101, 114, 101, 110, 99, 101, 115, 32, 116, 111, 32, 116, 104, 105, 115, 32, 99, 111,
            110, 115, 116, 97, 110, 116, 32, 109, 117, 115, 116, 32, 105, 110, 99, 108, 117, 100,
            101, 32, 0,
        ],
    };
static mut l_Lean_Linter_checkDeprecated___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__14_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [105, 116, 115, 32, 112, 114, 101, 102, 105, 120, 32, 96, 0],
    };
static mut l_Lean_Linter_checkDeprecated___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__16_value: leanh::LeanStringObject<34> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            96, 32, 101, 118, 101, 110, 32, 119, 104, 101, 110, 32, 105, 110, 115, 105, 100, 101,
            32, 105, 116, 115, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 46, 0,
        ],
    };
static mut l_Lean_Linter_checkDeprecated___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__18_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Lean_Linter_checkDeprecated___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__20_value: leanh::LeanStringObject<30> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            97, 116, 32, 108, 101, 97, 115, 116, 32, 116, 104, 101, 32, 108, 97, 115, 116, 32, 99,
            111, 109, 112, 111, 110, 101, 110, 116, 32, 96, 0,
        ],
    };
static mut l_Lean_Linter_checkDeprecated___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__22_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [96, 32, 111, 102, 32, 0],
    };
static mut l_Lean_Linter_checkDeprecated___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__22_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__24_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            32, 40, 101, 46, 103, 46, 44, 32, 102, 114, 111, 109, 32, 96, 120, 46, 0,
        ],
    };
static mut l_Lean_Linter_checkDeprecated___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__24_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__26_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [96, 32, 116, 111, 32, 96, 0],
    };
static mut l_Lean_Linter_checkDeprecated___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__26_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__28_value: leanh::LeanStringObject<5> =
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
        m_data: [32, 120, 96, 41, 0],
    };
static mut l_Lean_Linter_checkDeprecated___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__28_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Linter_checkDeprecated___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__30: u64 = 0;
pub static l_Lean_Linter_checkDeprecated___closed__31_value: leanh::LeanStringObject<43> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 43,
        m_capacity: 43,
        m_length: 42,
        m_data: [
            84, 104, 101, 32, 117, 112, 100, 97, 116, 101, 100, 32, 99, 111, 110, 115, 116, 97,
            110, 116, 32, 104, 97, 115, 32, 97, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116,
            32, 116, 121, 112, 101, 58, 0,
        ],
    };
static mut l_Lean_Linter_checkDeprecated___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__31_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__33_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [10, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 0],
    };
static mut l_Lean_Linter_checkDeprecated___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__33_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_checkDeprecated___closed__35_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [58, 32, 0],
    };
static mut l_Lean_Linter_checkDeprecated___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_checkDeprecated___closed__35_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Linter_checkDeprecated___closed__36_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_checkDeprecated___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(
    mut v_name_1579_: *mut leanh::LeanObject,
    mut v_decl_1580_: *mut leanh::LeanObject,
    mut v_ref_1581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v_unused_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1602_: u8 = 0;
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1583_ = leanh::lean_ctor_get(v_decl_1580_, 0);
                v_descr_1584_ = leanh::lean_ctor_get(v_decl_1580_, 1);
                v_deprecation_x3f_1585_ = leanh::lean_ctor_get(v_decl_1580_, 2);
                v___x_1586_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1587_ = (leanh::lean_unbox(v_defValue_1583_) as u8);
                leanh::lean_ctor_set_uint8(v___x_1586_, 0 as u32, v___x_1587_);
                leanh::lean_inc(v_deprecation_x3f_1585_);
                leanh::lean_inc_ref(v_descr_1584_);
                leanh::lean_inc_n(v_name_1579_, 2);
                v___x_1588_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_1588_, 0, v_name_1579_);
                leanh::lean_ctor_set(v___x_1588_, 1, v_ref_1581_);
                leanh::lean_ctor_set(v___x_1588_, 2, v___x_1586_);
                leanh::lean_ctor_set(v___x_1588_, 3, v_descr_1584_);
                leanh::lean_ctor_set(v___x_1588_, 4, v_deprecation_x3f_1585_);
                v___x_1589_ = lean_register_option(v_name_1579_, v___x_1588_);
                if leanh::lean_obj_tag(v___x_1589_) == 0 {
                    v_isSharedCheck_1597_ = (!leanh::lean_is_exclusive(v___x_1589_)) as u8;
                    if v_isSharedCheck_1597_ == 0 {
                        v_unused_1598_ = leanh::lean_ctor_get(v___x_1589_, 0);
                        leanh::lean_dec(v_unused_1598_);
                        v___x_1591_ = v___x_1589_;
                        v_isShared_1592_ = v_isSharedCheck_1597_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1589_);
                        v___x_1591_ = leanh::lean_box(0);
                        v_isShared_1592_ = v_isSharedCheck_1597_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_1579_);
                    v_a_1599_ = leanh::lean_ctor_get(v___x_1589_, 0);
                    v_isSharedCheck_1606_ = (!leanh::lean_is_exclusive(v___x_1589_)) as u8;
                    if v_isSharedCheck_1606_ == 0 {
                        v___x_1601_ = v___x_1589_;
                        v_isShared_1602_ = v_isSharedCheck_1606_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1599_);
                        leanh::lean_dec(v___x_1589_);
                        v___x_1601_ = leanh::lean_box(0);
                        v_isShared_1602_ = v_isSharedCheck_1606_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_1583_);
                v___x_1593_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1593_, 0, v_name_1579_);
                leanh::lean_ctor_set(v___x_1593_, 1, v_defValue_1583_);
                if v_isShared_1592_ == 0 {
                    leanh::lean_ctor_set(v___x_1591_, 0, v___x_1593_);
                    v___x_1595_ = v___x_1591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1596_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
                    v___x_1595_ = v_reuseFailAlloc_1596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1595_;
            }
            3 => {
                if v_isShared_1602_ == 0 {
                    v___x_1604_ = v___x_1601_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
                    v___x_1604_ = v_reuseFailAlloc_1605_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1607_: *mut leanh::LeanObject,
    mut v_decl_1608_: *mut leanh::LeanObject,
    mut v_ref_1609_: *mut leanh::LeanObject,
    mut v_a_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(v_name_1607_, v_decl_1608_, v_ref_1609_);
    leanh::lean_dec_ref(v_decl_1608_);
    return v_res_1611_;
}
pub unsafe fn l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_;
    v___x_1632_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_;
    v___x_1633_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_;
    v___x_1634_ = l_Lean_Option_register___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4__spec__0(v___x_1631_, v___x_1632_, v___x_1633_);
    return v___x_1634_;
}
pub unsafe fn l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4____boxed(
    mut v_a_1635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1636_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_();
    return v_res_1636_;
}
pub unsafe fn l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_(
    mut v_x_1641_: *mut leanh::LeanObject,
    mut v_x_1642_: *mut leanh::LeanObject,
    mut v_x_1643_: *mut leanh::LeanObject,
    mut v___y_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = leanh::lean_box(0);
    v___x_1647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1647_, 0, v___x_1646_);
    return v___x_1647_;
}
pub unsafe fn l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2____boxed(
    mut v_x_1648_: *mut leanh::LeanObject,
    mut v_x_1649_: *mut leanh::LeanObject,
    mut v_x_1650_: *mut leanh::LeanObject,
    mut v___y_1651_: *mut leanh::LeanObject,
    mut v___y_1652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1653_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_(v_x_1648_, v_x_1649_, v_x_1650_, v___y_1651_);
    leanh::lean_dec(v___y_1651_);
    leanh::lean_dec_ref(v_x_1650_);
    leanh::lean_dec_ref(v_x_1649_);
    leanh::lean_dec(v_x_1648_);
    return v_res_1653_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1654_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_1656_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1656_, 0, v___x_1655_);
    return v___x_1656_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1657_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_1658_ = leanh::lean_unsigned_to_nat(0);
    v___x_1659_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1659_, 0, v___x_1658_);
    leanh::lean_ctor_set(v___x_1659_, 1, v___x_1658_);
    leanh::lean_ctor_set(v___x_1659_, 2, v___x_1658_);
    leanh::lean_ctor_set(v___x_1659_, 3, v___x_1658_);
    leanh::lean_ctor_set(v___x_1659_, 4, v___x_1657_);
    leanh::lean_ctor_set(v___x_1659_, 5, v___x_1657_);
    leanh::lean_ctor_set(v___x_1659_, 6, v___x_1657_);
    leanh::lean_ctor_set(v___x_1659_, 7, v___x_1657_);
    leanh::lean_ctor_set(v___x_1659_, 8, v___x_1657_);
    leanh::lean_ctor_set(v___x_1659_, 9, v___x_1657_);
    return v___x_1659_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = leanh::lean_unsigned_to_nat(32);
    v___x_1661_ = lean_mk_empty_array_with_capacity(v___x_1660_);
    v___x_1662_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1662_, 0, v___x_1661_);
    return v___x_1662_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1663_: usize = 0;
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = 5usize;
    v___x_1664_ = leanh::lean_unsigned_to_nat(0);
    v___x_1665_ = leanh::lean_unsigned_to_nat(32);
    v___x_1666_ = lean_mk_empty_array_with_capacity(v___x_1665_);
    v___x_1667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_1668_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1668_, 0, v___x_1667_);
    leanh::lean_ctor_set(v___x_1668_, 1, v___x_1666_);
    leanh::lean_ctor_set(v___x_1668_, 2, v___x_1664_);
    leanh::lean_ctor_set(v___x_1668_, 3, v___x_1664_);
    leanh::lean_ctor_set_usize(v___x_1668_, 4, v___x_1663_);
    return v___x_1668_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = leanh::lean_box(1);
    v___x_1670_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_1671_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_1672_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1672_, 0, v___x_1671_);
    leanh::lean_ctor_set(v___x_1672_, 1, v___x_1670_);
    leanh::lean_ctor_set(v___x_1672_, 2, v___x_1669_);
    return v___x_1672_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
    mut v___y_1675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1677_ = lean_st_ref_get(v___y_1675_);
    v_env_1678_ = leanh::lean_ctor_get(v___x_1677_, 0);
    leanh::lean_inc_ref(v_env_1678_);
    leanh::lean_dec(v___x_1677_);
    v_options_1679_ = leanh::lean_ctor_get(v___y_1674_, 2);
    v___x_1680_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_1681_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_1679_);
    v___x_1682_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1682_, 0, v_env_1678_);
    leanh::lean_ctor_set(v___x_1682_, 1, v___x_1680_);
    leanh::lean_ctor_set(v___x_1682_, 2, v___x_1681_);
    leanh::lean_ctor_set(v___x_1682_, 3, v_options_1679_);
    v___x_1683_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1683_, 0, v___x_1682_);
    leanh::lean_ctor_set(v___x_1683_, 1, v_msgData_1673_);
    v___x_1684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1684_, 0, v___x_1683_);
    return v___x_1684_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
    mut v___y_1687_: *mut leanh::LeanObject,
    mut v___y_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1689_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1685_, v___y_1686_, v___y_1687_);
    leanh::lean_dec(v___y_1687_);
    leanh::lean_dec_ref(v___y_1686_);
    return v_res_1689_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__0()
-> f64 {
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: f64 = 0.0;
    v___x_1690_ = leanh::lean_unsigned_to_nat(0);
    v___x_1691_ = lean_float_of_nat(v___x_1690_);
    return v___x_1691_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7(
    mut v_cls_1695_: *mut leanh::LeanObject,
    mut v_msg_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v_tid_1719_: u64 = 0;
    let mut v_traces_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: f64 = 0.0;
    let mut v___x_1726_: u8 = 0;
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1744_: u8 = 0;
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1700_ = leanh::lean_ctor_get(v___y_1697_, 5);
                v___x_1701_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0(v_msg_1696_, v___y_1697_, v___y_1698_);
                v_a_1702_ = leanh::lean_ctor_get(v___x_1701_, 0);
                v_isSharedCheck_1746_ = (!leanh::lean_is_exclusive(v___x_1701_)) as u8;
                if v_isSharedCheck_1746_ == 0 {
                    v___x_1704_ = v___x_1701_;
                    v_isShared_1705_ = v_isSharedCheck_1746_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1702_);
                    leanh::lean_dec(v___x_1701_);
                    v___x_1704_ = leanh::lean_box(0);
                    v_isShared_1705_ = v_isSharedCheck_1746_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1706_ = lean_st_ref_take(v___y_1698_);
                v_traceState_1707_ = leanh::lean_ctor_get(v___x_1706_, 4);
                v_env_1708_ = leanh::lean_ctor_get(v___x_1706_, 0);
                v_nextMacroScope_1709_ = leanh::lean_ctor_get(v___x_1706_, 1);
                v_ngen_1710_ = leanh::lean_ctor_get(v___x_1706_, 2);
                v_auxDeclNGen_1711_ = leanh::lean_ctor_get(v___x_1706_, 3);
                v_cache_1712_ = leanh::lean_ctor_get(v___x_1706_, 5);
                v_messages_1713_ = leanh::lean_ctor_get(v___x_1706_, 6);
                v_infoState_1714_ = leanh::lean_ctor_get(v___x_1706_, 7);
                v_snapshotTasks_1715_ = leanh::lean_ctor_get(v___x_1706_, 8);
                v_isSharedCheck_1745_ = (!leanh::lean_is_exclusive(v___x_1706_)) as u8;
                if v_isSharedCheck_1745_ == 0 {
                    v___x_1717_ = v___x_1706_;
                    v_isShared_1718_ = v_isSharedCheck_1745_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1715_);
                    leanh::lean_inc(v_infoState_1714_);
                    leanh::lean_inc(v_messages_1713_);
                    leanh::lean_inc(v_cache_1712_);
                    leanh::lean_inc(v_traceState_1707_);
                    leanh::lean_inc(v_auxDeclNGen_1711_);
                    leanh::lean_inc(v_ngen_1710_);
                    leanh::lean_inc(v_nextMacroScope_1709_);
                    leanh::lean_inc(v_env_1708_);
                    leanh::lean_dec(v___x_1706_);
                    v___x_1717_ = leanh::lean_box(0);
                    v_isShared_1718_ = v_isSharedCheck_1745_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1719_ = leanh::lean_ctor_get_uint64(
                    v_traceState_1707_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1720_ = leanh::lean_ctor_get(v_traceState_1707_, 0);
                v_isSharedCheck_1744_ =
                    (!leanh::lean_is_exclusive(v_traceState_1707_)) as u8;
                if v_isSharedCheck_1744_ == 0 {
                    v___x_1722_ = v_traceState_1707_;
                    v_isShared_1723_ = v_isSharedCheck_1744_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_1720_);
                    leanh::lean_dec(v_traceState_1707_);
                    v___x_1722_ = leanh::lean_box(0);
                    v_isShared_1723_ = v_isSharedCheck_1744_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1724_ = leanh::lean_box(0);
                v___x_1725_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__0);
                v___x_1726_ = 0;
                v___x_1727_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__1;
                v___x_1728_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_1728_, 0, v_cls_1695_);
                leanh::lean_ctor_set(v___x_1728_, 1, v___x_1724_);
                leanh::lean_ctor_set(v___x_1728_, 2, v___x_1727_);
                leanh::lean_ctor_set_float(
                    v___x_1728_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1725_,
                );
                leanh::lean_ctor_set_float(
                    v___x_1728_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1725_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1728_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1726_,
                );
                v___x_1729_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__2;
                v___x_1730_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1730_, 0, v___x_1728_);
                leanh::lean_ctor_set(v___x_1730_, 1, v_a_1702_);
                leanh::lean_ctor_set(v___x_1730_, 2, v___x_1729_);
                leanh::lean_inc(v_ref_1700_);
                v___x_1731_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1731_, 0, v_ref_1700_);
                leanh::lean_ctor_set(v___x_1731_, 1, v___x_1730_);
                v___x_1732_ = l_Lean_PersistentArray_push___redArg(v_traces_1720_, v___x_1731_);
                if v_isShared_1723_ == 0 {
                    leanh::lean_ctor_set(v___x_1722_, 0, v___x_1732_);
                    v___x_1734_ = v___x_1722_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1743_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1732_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1743_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_1719_,
                    );
                    v___x_1734_ = v_reuseFailAlloc_1743_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1718_ == 0 {
                    leanh::lean_ctor_set(v___x_1717_, 4, v___x_1734_);
                    v___x_1736_ = v___x_1717_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_env_1708_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_nextMacroScope_1709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_ngen_1710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_auxDeclNGen_1711_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 4, v___x_1734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 5, v_cache_1712_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 6, v_messages_1713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 7, v_infoState_1714_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 8, v_snapshotTasks_1715_);
                    v___x_1736_ = v_reuseFailAlloc_1742_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1737_ = lean_st_ref_set(v___y_1698_, v___x_1736_);
                v___x_1738_ = leanh::lean_box(0);
                if v_isShared_1705_ == 0 {
                    leanh::lean_ctor_set(v___x_1704_, 0, v___x_1738_);
                    v___x_1740_ = v___x_1704_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
                    v___x_1740_ = v_reuseFailAlloc_1741_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___boxed(
    mut v_cls_1747_: *mut leanh::LeanObject,
    mut v_msg_1748_: *mut leanh::LeanObject,
    mut v___y_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1752_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7(v_cls_1747_, v_msg_1748_, v___y_1749_, v___y_1750_);
    leanh::lean_dec(v___y_1750_);
    leanh::lean_dec_ref(v___y_1749_);
    return v_res_1752_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8_spec__11___redArg(
    mut v_keys_1753_: *mut leanh::LeanObject,
    mut v_i_1754_: *mut leanh::LeanObject,
    mut v_k_1755_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: u8 = 0;
    let mut v_k_x27_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: u8 = 0;
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1756_ = lean_array_get_size(v_keys_1753_);
                v___x_1757_ = lean_nat_dec_lt(v_i_1754_, v___x_1756_);
                if v___x_1757_ == 0 {
                    leanh::lean_dec(v_i_1754_);
                    return v___x_1757_;
                } else {
                    v_k_x27_1758_ = lean_array_fget_borrowed(v_keys_1753_, v_i_1754_);
                    v___x_1759_ = l_Lean_instBEqExtraModUse_beq(v_k_1755_, v_k_x27_1758_);
                    if v___x_1759_ == 0 {
                        v___x_1760_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1761_ = lean_nat_add(v_i_1754_, v___x_1760_);
                        leanh::lean_dec(v_i_1754_);
                        v_i_1754_ = v___x_1761_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_1754_);
                        return v___x_1759_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8_spec__11___redArg___boxed(
    mut v_keys_1763_: *mut leanh::LeanObject,
    mut v_i_1764_: *mut leanh::LeanObject,
    mut v_k_1765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1766_: u8 = 0;
    let mut v_r_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8_spec__11___redArg(v_keys_1763_, v_i_1764_, v_k_1765_);
    leanh::lean_dec_ref(v_k_1765_);
    leanh::lean_dec_ref(v_keys_1763_);
    v_r_1767_ = leanh::lean_box((v_res_1766_) as usize);
    return v_r_1767_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__0()
-> usize {
    let mut v___x_1768_: usize = 0;
    let mut v___x_1769_: usize = 0;
    let mut v___x_1770_: usize = 0;
    v___x_1768_ = 5usize;
    v___x_1769_ = 1usize;
    v___x_1770_ = lean_usize_shift_left(v___x_1769_, v___x_1768_);
    return v___x_1770_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__1()
-> usize {
    let mut v___x_1771_: usize = 0;
    let mut v___x_1772_: usize = 0;
    let mut v___x_1773_: usize = 0;
    v___x_1771_ = 1usize;
    v___x_1772_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__0);
    v___x_1773_ = lean_usize_sub(v___x_1772_, v___x_1771_);
    return v___x_1773_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg(
    mut v_x_1774_: *mut leanh::LeanObject,
    mut v_x_1775_: usize,
    mut v_x_1776_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: usize = 0;
    let mut v___x_1780_: usize = 0;
    let mut v___x_1781_: usize = 0;
    let mut v_j_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    let mut v_node_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: usize = 0;
    let mut v___x_1789_: u8 = 0;
    let mut v_ks_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1774_) == 0 {
                    v_es_1777_ = leanh::lean_ctor_get(v_x_1774_, 0);
                    v___x_1778_ = leanh::lean_box(2);
                    v___x_1779_ = 5usize;
                    v___x_1780_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___closed__1);
                    v___x_1781_ = lean_usize_land(v_x_1775_, v___x_1780_);
                    v_j_1782_ = lean_usize_to_nat(v___x_1781_);
                    v___x_1783_ = lean_array_get_borrowed(v___x_1778_, v_es_1777_, v_j_1782_);
                    leanh::lean_dec(v_j_1782_);
                    match leanh::lean_obj_tag(v___x_1783_) {
                        0 => {
                            v_key_1784_ = leanh::lean_ctor_get(v___x_1783_, 0);
                            v___x_1785_ = l_Lean_instBEqExtraModUse_beq(v_x_1776_, v_key_1784_);
                            return v___x_1785_;
                        }
                        1 => {
                            v_node_1786_ = leanh::lean_ctor_get(v___x_1783_, 0);
                            v___x_1787_ = lean_usize_shift_right(v_x_1775_, v___x_1779_);
                            v_x_1774_ = v_node_1786_;
                            v_x_1775_ = v___x_1787_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1789_ = 0;
                            return v___x_1789_;
                        }
                    }
                } else {
                    v_ks_1790_ = leanh::lean_ctor_get(v_x_1774_, 0);
                    v___x_1791_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1792_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8_spec__11___redArg(v_ks_1790_, v___x_1791_, v_x_1776_);
                    return v___x_1792_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_x_1793_: *mut leanh::LeanObject,
    mut v_x_1794_: *mut leanh::LeanObject,
    mut v_x_1795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_8729__boxed_1796_: usize = 0;
    let mut v_res_1797_: u8 = 0;
    let mut v_r_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_8729__boxed_1796_ = leanh::lean_unbox_usize(v_x_1794_);
    leanh::lean_dec(v_x_1794_);
    v_res_1797_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg(v_x_1793_, v_x_8729__boxed_1796_, v_x_1795_);
    leanh::lean_dec_ref(v_x_1795_);
    leanh::lean_dec_ref(v_x_1793_);
    v_r_1798_ = leanh::lean_box((v_res_1797_) as usize);
    return v_r_1798_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6___redArg(
    mut v_x_1799_: *mut leanh::LeanObject,
    mut v_x_1800_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1801_: u64 = 0;
    let mut v___x_1802_: usize = 0;
    let mut v___x_1803_: u8 = 0;
    v___x_1801_ = l_Lean_instHashableExtraModUse_hash(v_x_1800_);
    v___x_1802_ = lean_uint64_to_usize(v___x_1801_);
    v___x_1803_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg(v_x_1799_, v___x_1802_, v_x_1800_);
    return v___x_1803_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6___redArg___boxed(
    mut v_x_1804_: *mut leanh::LeanObject,
    mut v_x_1805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1806_: u8 = 0;
    let mut v_r_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1806_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6___redArg(v_x_1804_, v_x_1805_);
    leanh::lean_dec_ref(v_x_1805_);
    leanh::lean_dec_ref(v_x_1804_);
    v_r_1807_ = leanh::lean_box((v_res_1806_) as usize);
    return v_r_1807_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__1;
    v___x_1811_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__0;
    v___x_1812_ = l_Lean_PersistentHashMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1811_,
        v___x_1810_,
    );
    return v___x_1812_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1813_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1813_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__3);
    v___x_1815_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1815_, 0, v___x_1814_);
    return v___x_1815_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__4);
    v___x_1817_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1817_, 0, v___x_1816_);
    leanh::lean_ctor_set(v___x_1817_, 1, v___x_1816_);
    return v___x_1817_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__8;
    v___x_1823_ = l_Lean_stringToMessageData(v___x_1822_);
    return v___x_1823_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__10;
    v___x_1826_ = l_Lean_stringToMessageData(v___x_1825_);
    return v___x_1826_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__1;
    v___x_1828_ = l_Lean_stringToMessageData(v___x_1827_);
    return v___x_1828_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__15()
-> *mut leanh::LeanObject {
    let mut v_cls_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cls_1832_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__7;
    v___x_1833_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__14;
    v___x_1834_ = l_Lean_Name_append(v___x_1833_, v_cls_1832_);
    return v___x_1834_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__16;
    v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
    return v___x_1837_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__18;
    v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
    return v___x_1840_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4(
    mut v_mod_1845_: *mut leanh::LeanObject,
    mut v_isMeta_1846_: u8,
    mut v_hint_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
    mut v___y_1849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_1853_: u8 = 0;
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v_asyncMode_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v_unused_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: u8 = 0;
    let mut v_options_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1890_: u8 = 0;
    let mut v_inheritedTraceOptions_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: u8 = 0;
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1851_ = lean_st_ref_get(v___y_1849_);
                v_env_1852_ = leanh::lean_ctor_get(v___x_1851_, 0);
                leanh::lean_inc_ref(v_env_1852_);
                leanh::lean_dec(v___x_1851_);
                v_isExporting_1853_ = leanh::lean_ctor_get_uint8(
                    v_env_1852_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_1852_);
                v___x_1854_ = lean_st_ref_get(v___y_1849_);
                v_env_1855_ = leanh::lean_ctor_get(v___x_1854_, 0);
                leanh::lean_inc_ref(v_env_1855_);
                leanh::lean_dec(v___x_1854_);
                v___x_1856_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__2);
                leanh::lean_inc(v_mod_1845_);
                v_entry_1857_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                leanh::lean_ctor_set(v_entry_1857_, 0, v_mod_1845_);
                leanh::lean_ctor_set_uint8(
                    v_entry_1857_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_isExporting_1853_,
                );
                leanh::lean_ctor_set_uint8(
                    v_entry_1857_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_1846_,
                );
                v___x_1858_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_1859_ = leanh::lean_box(1);
                v___x_1860_ = leanh::lean_box(0);
                v___x_1887_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_1856_,
                    v___x_1858_,
                    v_env_1855_,
                    v___x_1859_,
                    v___x_1860_,
                );
                v___x_1888_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6___redArg(v___x_1887_, v_entry_1857_);
                leanh::lean_dec(v___x_1887_);
                if v___x_1888_ == 0 {
                    v_options_1889_ = leanh::lean_ctor_get(v___y_1848_, 2);
                    v_hasTrace_1890_ = leanh::lean_ctor_get_uint8(
                        v_options_1889_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_1890_ == 0 {
                        leanh::lean_dec(v_hint_1847_);
                        leanh::lean_dec(v_mod_1845_);
                        v___y_1862_ = v___y_1849_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_1891_ =
                            leanh::lean_ctor_get(v___y_1848_, 13);
                        v_cls_1892_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__7;
                        v___x_1912_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__15), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__15_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__15);
                        v___x_1913_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_1891_,
                            v_options_1889_,
                            v___x_1912_,
                        );
                        if v___x_1913_ == 0 {
                            leanh::lean_dec(v_hint_1847_);
                            leanh::lean_dec(v_mod_1845_);
                            v___y_1862_ = v___y_1849_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1914_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__17), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__17_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__17);
                            if v_isExporting_1853_ == 0 {
                                v___x_1923_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__22;
                                v___y_1916_ = v___x_1923_;
                                state = 6;
                                continue;
                            } else {
                                v___x_1924_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__23;
                                v___y_1916_ = v___x_1924_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v_entry_1857_, 1);
                    leanh::lean_dec(v_hint_1847_);
                    leanh::lean_dec(v_mod_1845_);
                    v___x_1925_ = leanh::lean_box(0);
                    v___x_1926_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1926_, 0, v___x_1925_);
                    return v___x_1926_;
                }
            }
            1 => {
                v___x_1863_ = lean_st_ref_take(v___y_1862_);
                v_toEnvExtension_1864_ = leanh::lean_ctor_get(v___x_1858_, 0);
                v_env_1865_ = leanh::lean_ctor_get(v___x_1863_, 0);
                v_nextMacroScope_1866_ = leanh::lean_ctor_get(v___x_1863_, 1);
                v_ngen_1867_ = leanh::lean_ctor_get(v___x_1863_, 2);
                v_auxDeclNGen_1868_ = leanh::lean_ctor_get(v___x_1863_, 3);
                v_traceState_1869_ = leanh::lean_ctor_get(v___x_1863_, 4);
                v_messages_1870_ = leanh::lean_ctor_get(v___x_1863_, 6);
                v_infoState_1871_ = leanh::lean_ctor_get(v___x_1863_, 7);
                v_snapshotTasks_1872_ = leanh::lean_ctor_get(v___x_1863_, 8);
                v_isSharedCheck_1885_ = (!leanh::lean_is_exclusive(v___x_1863_)) as u8;
                if v_isSharedCheck_1885_ == 0 {
                    v_unused_1886_ = leanh::lean_ctor_get(v___x_1863_, 5);
                    leanh::lean_dec(v_unused_1886_);
                    v___x_1874_ = v___x_1863_;
                    v_isShared_1875_ = v_isSharedCheck_1885_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1872_);
                    leanh::lean_inc(v_infoState_1871_);
                    leanh::lean_inc(v_messages_1870_);
                    leanh::lean_inc(v_traceState_1869_);
                    leanh::lean_inc(v_auxDeclNGen_1868_);
                    leanh::lean_inc(v_ngen_1867_);
                    leanh::lean_inc(v_nextMacroScope_1866_);
                    leanh::lean_inc(v_env_1865_);
                    leanh::lean_dec(v___x_1863_);
                    v___x_1874_ = leanh::lean_box(0);
                    v_isShared_1875_ = v_isSharedCheck_1885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_1876_ = leanh::lean_ctor_get(v_toEnvExtension_1864_, 2);
                v___x_1877_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_1858_,
                    v_env_1865_,
                    v_entry_1857_,
                    v_asyncMode_1876_,
                    v___x_1860_,
                );
                v___x_1878_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__5);
                if v_isShared_1875_ == 0 {
                    leanh::lean_ctor_set(v___x_1874_, 5, v___x_1878_);
                    leanh::lean_ctor_set(v___x_1874_, 0, v___x_1877_);
                    v___x_1880_ = v___x_1874_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_nextMacroScope_1866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_ngen_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 3, v_auxDeclNGen_1868_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 4, v_traceState_1869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 5, v___x_1878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 6, v_messages_1870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 7, v_infoState_1871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 8, v_snapshotTasks_1872_);
                    v___x_1880_ = v_reuseFailAlloc_1884_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1881_ = lean_st_ref_set(v___y_1862_, v___x_1880_);
                v___x_1882_ = leanh::lean_box(0);
                v___x_1883_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1883_, 0, v___x_1882_);
                return v___x_1883_;
            }
            4 => {
                v___x_1896_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1896_, 0, v___y_1894_);
                leanh::lean_ctor_set(v___x_1896_, 1, v___y_1895_);
                v___x_1897_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7(v_cls_1892_, v___x_1896_, v___y_1848_, v___y_1849_);
                if leanh::lean_obj_tag(v___x_1897_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1897_, 1);
                    v___y_1862_ = v___y_1849_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_entry_1857_, 1);
                    return v___x_1897_;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___y_1900_);
                v___x_1901_ = l_Lean_stringToMessageData(v___y_1900_);
                v___x_1902_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1902_, 0, v___y_1899_);
                leanh::lean_ctor_set(v___x_1902_, 1, v___x_1901_);
                v___x_1903_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__9);
                v___x_1904_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1904_, 0, v___x_1902_);
                leanh::lean_ctor_set(v___x_1904_, 1, v___x_1903_);
                v___x_1905_ = l_Lean_MessageData_ofName(v_mod_1845_);
                v___x_1906_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1906_, 0, v___x_1904_);
                leanh::lean_ctor_set(v___x_1906_, 1, v___x_1905_);
                v___x_1907_ = l_Lean_Name_isAnonymous(v_hint_1847_);
                if v___x_1907_ == 0 {
                    v___x_1908_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__11), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__11_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__11);
                    v___x_1909_ = l_Lean_MessageData_ofName(v_hint_1847_);
                    v___x_1910_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1910_, 0, v___x_1908_);
                    leanh::lean_ctor_set(v___x_1910_, 1, v___x_1909_);
                    v___y_1894_ = v___x_1906_;
                    v___y_1895_ = v___x_1910_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_hint_1847_);
                    v___x_1911_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__12);
                    v___y_1894_ = v___x_1906_;
                    v___y_1895_ = v___x_1911_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v___y_1916_);
                v___x_1917_ = l_Lean_stringToMessageData(v___y_1916_);
                v___x_1918_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1918_, 0, v___x_1914_);
                leanh::lean_ctor_set(v___x_1918_, 1, v___x_1917_);
                v___x_1919_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__19), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__19_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__19);
                v___x_1920_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1920_, 0, v___x_1918_);
                leanh::lean_ctor_set(v___x_1920_, 1, v___x_1919_);
                if v_isMeta_1846_ == 0 {
                    v___x_1921_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__20;
                    v___y_1899_ = v___x_1920_;
                    v___y_1900_ = v___x_1921_;
                    state = 5;
                    continue;
                } else {
                    v___x_1922_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__21;
                    v___y_1899_ = v___x_1920_;
                    v___y_1900_ = v___x_1922_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___boxed(
    mut v_mod_1927_: *mut leanh::LeanObject,
    mut v_isMeta_1928_: *mut leanh::LeanObject,
    mut v_hint_1929_: *mut leanh::LeanObject,
    mut v___y_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_1933_: u8 = 0;
    let mut v_res_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_1933_ = (leanh::lean_unbox(v_isMeta_1928_) as u8);
    v_res_1934_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4(v_mod_1927_, v_isMeta_boxed_1933_, v_hint_1929_, v___y_1930_, v___y_1931_);
    leanh::lean_dec(v___y_1931_);
    leanh::lean_dec_ref(v___y_1930_);
    return v_res_1934_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6_spec__10___redArg(
    mut v_a_1935_: *mut leanh::LeanObject,
    mut v_x_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1936_) == 0 {
                    v___x_1937_ = leanh::lean_box(0);
                    return v___x_1937_;
                } else {
                    v_key_1938_ = leanh::lean_ctor_get(v_x_1936_, 0);
                    v_value_1939_ = leanh::lean_ctor_get(v_x_1936_, 1);
                    v_tail_1940_ = leanh::lean_ctor_get(v_x_1936_, 2);
                    v___x_1941_ = lean_name_eq(v_key_1938_, v_a_1935_);
                    if v___x_1941_ == 0 {
                        v_x_1936_ = v_tail_1940_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1939_);
                        v___x_1943_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1943_, 0, v_value_1939_);
                        return v___x_1943_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6_spec__10___redArg___boxed(
    mut v_a_1944_: *mut leanh::LeanObject,
    mut v_x_1945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1946_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6_spec__10___redArg(v_a_1944_, v_x_1945_);
    leanh::lean_dec(v_x_1945_);
    leanh::lean_dec(v_a_1944_);
    return v_res_1946_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg___closed__0()
-> u64 {
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: u64 = 0;
    v___x_1947_ = leanh::lean_unsigned_to_nat(1723);
    v___x_1948_ = lean_uint64_of_nat(v___x_1947_);
    return v___x_1948_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg(
    mut v_m_1949_: *mut leanh::LeanObject,
    mut v_a_1950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1954_: u64 = 0;
    let mut v___x_1955_: u64 = 0;
    let mut v___x_1956_: u64 = 0;
    let mut v_fold_1957_: u64 = 0;
    let mut v___x_1958_: u64 = 0;
    let mut v___x_1959_: u64 = 0;
    let mut v___x_1960_: u64 = 0;
    let mut v___x_1961_: usize = 0;
    let mut v___x_1962_: usize = 0;
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: usize = 0;
    let mut v___x_1965_: usize = 0;
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u64 = 0;
    let mut v_hash_1969_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1951_ = leanh::lean_ctor_get(v_m_1949_, 1);
                v___x_1952_ = lean_array_get_size(v_buckets_1951_);
                if leanh::lean_obj_tag(v_a_1950_) == 0 {
                    v___x_1968_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg___closed__0);
                    v___y_1954_ = v___x_1968_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1969_ = leanh::lean_ctor_get_uint64(
                        v_a_1950_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1954_ = v_hash_1969_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1955_ = 32u64;
                v___x_1956_ = lean_uint64_shift_right(v___y_1954_, v___x_1955_);
                v_fold_1957_ = lean_uint64_xor(v___y_1954_, v___x_1956_);
                v___x_1958_ = 16u64;
                v___x_1959_ = lean_uint64_shift_right(v_fold_1957_, v___x_1958_);
                v___x_1960_ = lean_uint64_xor(v_fold_1957_, v___x_1959_);
                v___x_1961_ = lean_uint64_to_usize(v___x_1960_);
                v___x_1962_ = lean_usize_of_nat(v___x_1952_);
                v___x_1963_ = 1usize;
                v___x_1964_ = lean_usize_sub(v___x_1962_, v___x_1963_);
                v___x_1965_ = lean_usize_land(v___x_1961_, v___x_1964_);
                v___x_1966_ = lean_array_uget_borrowed(v_buckets_1951_, v___x_1965_);
                v___x_1967_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6_spec__10___redArg(v_a_1950_, v___x_1966_);
                return v___x_1967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg___boxed(
    mut v_m_1970_: *mut leanh::LeanObject,
    mut v_a_1971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_1970_, v_a_1971_);
    leanh::lean_dec(v_a_1971_);
    leanh::lean_dec_ref(v_m_1970_);
    return v_res_1972_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__5(
    mut v___x_1973_: *mut leanh::LeanObject,
    mut v_declName_1974_: *mut leanh::LeanObject,
    mut v_as_1975_: *mut leanh::LeanObject,
    mut v_sz_1976_: usize,
    mut v_i_1977_: usize,
    mut v_b_1978_: *mut leanh::LeanObject,
    mut v___y_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1982_: u8 = 0;
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1982_ = lean_usize_dec_lt(v_i_1977_, v_sz_1976_);
                if v___x_1982_ == 0 {
                    leanh::lean_dec(v_declName_1974_);
                    v___x_1983_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1983_, 0, v_b_1978_);
                    return v___x_1983_;
                } else {
                    v___x_1984_ = l_Lean_Environment_header(v___x_1973_);
                    v_modules_1985_ = leanh::lean_ctor_get(v___x_1984_, 3);
                    leanh::lean_inc_ref(v_modules_1985_);
                    leanh::lean_dec_ref(v___x_1984_);
                    v___x_1986_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_1987_ = lean_array_uget_borrowed(v_as_1975_, v_i_1977_);
                    v___x_1988_ = lean_array_get(v___x_1986_, v_modules_1985_, v_a_1987_);
                    leanh::lean_dec_ref(v_modules_1985_);
                    v_toImport_1989_ = leanh::lean_ctor_get(v___x_1988_, 0);
                    leanh::lean_inc_ref(v_toImport_1989_);
                    leanh::lean_dec(v___x_1988_);
                    v_module_1990_ = leanh::lean_ctor_get(v_toImport_1989_, 0);
                    leanh::lean_inc(v_module_1990_);
                    leanh::lean_dec_ref(v_toImport_1989_);
                    v___x_1991_ = 0;
                    leanh::lean_inc(v_declName_1974_);
                    v___x_1992_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4(v_module_1990_, v___x_1991_, v_declName_1974_, v___y_1979_, v___y_1980_);
                    if leanh::lean_obj_tag(v___x_1992_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1992_, 1);
                        v___x_1993_ = leanh::lean_box(0);
                        v___x_1994_ = 1usize;
                        v___x_1995_ = lean_usize_add(v_i_1977_, v___x_1994_);
                        v_i_1977_ = v___x_1995_;
                        v_b_1978_ = v___x_1993_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_declName_1974_);
                        return v___x_1992_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__5___boxed(
    mut v___x_1997_: *mut leanh::LeanObject,
    mut v_declName_1998_: *mut leanh::LeanObject,
    mut v_as_1999_: *mut leanh::LeanObject,
    mut v_sz_2000_: *mut leanh::LeanObject,
    mut v_i_2001_: *mut leanh::LeanObject,
    mut v_b_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2006_: usize = 0;
    let mut v_i_boxed_2007_: usize = 0;
    let mut v_res_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2006_ = leanh::lean_unbox_usize(v_sz_2000_);
    leanh::lean_dec(v_sz_2000_);
    v_i_boxed_2007_ = leanh::lean_unbox_usize(v_i_2001_);
    leanh::lean_dec(v_i_2001_);
    v_res_2008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__5(v___x_1997_, v_declName_1998_, v_as_1999_, v_sz_boxed_2006_, v_i_boxed_2007_, v_b_2002_, v___y_2003_, v___y_2004_);
    leanh::lean_dec(v___y_2004_);
    leanh::lean_dec_ref(v___y_2003_);
    leanh::lean_dec_ref(v_as_1999_);
    leanh::lean_dec_ref(v___x_1997_);
    return v_res_2008_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2011_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__1;
    v___x_2012_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__0;
    v___x_2013_ = l_Std_HashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2012_,
        v___x_2011_,
    );
    return v___x_2013_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2(
    mut v_declName_2016_: *mut leanh::LeanObject,
    mut v_isMeta_2017_: u8,
    mut v___y_2018_: *mut leanh::LeanObject,
    mut v___y_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2029_: usize = 0;
    let mut v___x_2030_: usize = 0;
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_unused_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2051_: u8 = 0;
    let mut v_toImport_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2021_ = lean_st_ref_get(v___y_2019_);
                v_env_2025_ = leanh::lean_ctor_get(v___x_2021_, 0);
                leanh::lean_inc_ref(v_env_2025_);
                leanh::lean_dec(v___x_2021_);
                v___x_2040_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2025_, v_declName_2016_);
                if leanh::lean_obj_tag(v___x_2040_) == 0 {
                    leanh::lean_dec_ref(v_env_2025_);
                    leanh::lean_dec(v_declName_2016_);
                    state = 1;
                    continue;
                } else {
                    v_val_2041_ = leanh::lean_ctor_get(v___x_2040_, 0);
                    leanh::lean_inc(v_val_2041_);
                    leanh::lean_dec_ref_known(v___x_2040_, 1);
                    v___x_2042_ = l_Lean_Environment_header(v_env_2025_);
                    v_modules_2043_ = leanh::lean_ctor_get(v___x_2042_, 3);
                    leanh::lean_inc_ref(v_modules_2043_);
                    leanh::lean_dec_ref(v___x_2042_);
                    v___x_2044_ = lean_array_get_size(v_modules_2043_);
                    v___x_2045_ = lean_nat_dec_lt(v_val_2041_, v___x_2044_);
                    if v___x_2045_ == 0 {
                        leanh::lean_dec_ref(v_modules_2043_);
                        leanh::lean_dec(v_val_2041_);
                        leanh::lean_dec_ref(v_env_2025_);
                        leanh::lean_dec(v_declName_2016_);
                        state = 1;
                        continue;
                    } else {
                        v___x_2046_ = lean_st_ref_get(v___y_2019_);
                        v_env_2047_ = leanh::lean_ctor_get(v___x_2046_, 0);
                        leanh::lean_inc_ref(v_env_2047_);
                        leanh::lean_dec(v___x_2046_);
                        v___x_2048_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__2);
                        v___x_2049_ = lean_array_fget(v_modules_2043_, v_val_2041_);
                        leanh::lean_dec(v_val_2041_);
                        leanh::lean_dec_ref(v_modules_2043_);
                        if v_isMeta_2017_ == 0 {
                            leanh::lean_dec_ref(v_env_2047_);
                            v___y_2051_ = v_isMeta_2017_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_declName_2016_);
                            v___x_2062_ = l_Lean_isMarkedMeta(v_env_2047_, v_declName_2016_);
                            if v___x_2062_ == 0 {
                                v___y_2051_ = v_isMeta_2017_;
                                state = 5;
                                continue;
                            } else {
                                v___x_2063_ = 0;
                                v___y_2051_ = v___x_2063_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2023_ = leanh::lean_box(0);
                v___x_2024_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2024_, 0, v___x_2023_);
                return v___x_2024_;
            }
            2 => {
                v___x_2028_ = leanh::lean_box(0);
                v_sz_2029_ = lean_array_size(v___y_2027_);
                v___x_2030_ = 0usize;
                v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__5(v_env_2025_, v_declName_2016_, v___y_2027_, v_sz_2029_, v___x_2030_, v___x_2028_, v___y_2018_, v___y_2019_);
                leanh::lean_dec_ref(v___y_2027_);
                leanh::lean_dec_ref(v_env_2025_);
                if leanh::lean_obj_tag(v___x_2031_) == 0 {
                    v_isSharedCheck_2038_ = (!leanh::lean_is_exclusive(v___x_2031_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v_unused_2039_ = leanh::lean_ctor_get(v___x_2031_, 0);
                        leanh::lean_dec(v_unused_2039_);
                        v___x_2033_ = v___x_2031_;
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2031_);
                        v___x_2033_ = leanh::lean_box(0);
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_2031_;
                }
            }
            3 => {
                if v_isShared_2034_ == 0 {
                    leanh::lean_ctor_set(v___x_2033_, 0, v___x_2028_);
                    v___x_2036_ = v___x_2033_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2028_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2036_;
            }
            5 => {
                v_toImport_2052_ = leanh::lean_ctor_get(v___x_2049_, 0);
                leanh::lean_inc_ref(v_toImport_2052_);
                leanh::lean_dec(v___x_2049_);
                v_module_2053_ = leanh::lean_ctor_get(v_toImport_2052_, 0);
                leanh::lean_inc(v_module_2053_);
                leanh::lean_dec_ref(v_toImport_2052_);
                leanh::lean_inc(v_declName_2016_);
                v___x_2054_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4(v_module_2053_, v___y_2051_, v_declName_2016_, v___y_2018_, v___y_2019_);
                if leanh::lean_obj_tag(v___x_2054_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2054_, 1);
                    v___x_2055_ = l_Lean_indirectModUseExt;
                    v___x_2056_ = leanh::lean_box(1);
                    v___x_2057_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_env_2025_);
                    v___x_2058_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_2048_,
                        v___x_2055_,
                        v_env_2025_,
                        v___x_2056_,
                        v___x_2057_,
                    );
                    v___x_2059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg(v___x_2058_, v_declName_2016_);
                    leanh::lean_dec(v___x_2058_);
                    if leanh::lean_obj_tag(v___x_2059_) == 0 {
                        v___x_2060_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___closed__3;
                        v___y_2027_ = v___x_2060_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2061_ = leanh::lean_ctor_get(v___x_2059_, 0);
                        leanh::lean_inc(v_val_2061_);
                        leanh::lean_dec_ref_known(v___x_2059_, 1);
                        v___y_2027_ = v_val_2061_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2025_);
                    leanh::lean_dec(v_declName_2016_);
                    return v___x_2054_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2___boxed(
    mut v_declName_2064_: *mut leanh::LeanObject,
    mut v_isMeta_2065_: *mut leanh::LeanObject,
    mut v___y_2066_: *mut leanh::LeanObject,
    mut v___y_2067_: *mut leanh::LeanObject,
    mut v___y_2068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_2069_: u8 = 0;
    let mut v_res_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2069_ = (leanh::lean_unbox(v_isMeta_2065_) as u8);
    v_res_2070_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2(v_declName_2064_, v_isMeta_boxed_2069_, v___y_2066_, v___y_2067_);
    leanh::lean_dec(v___y_2067_);
    leanh::lean_dec_ref(v___y_2066_);
    return v_res_2070_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0(
    mut v___y_2078_: u8,
    mut v_suppressElabErrors_2079_: u8,
    mut v_x_2080_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2080_) == 1 {
        let mut v_pre_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_2081_ = leanh::lean_ctor_get(v_x_2080_, 0);
        match leanh::lean_obj_tag(v_pre_2081_) {
            1 => {
                let mut v_pre_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_2082_ = leanh::lean_ctor_get(v_pre_2081_, 0);
                match leanh::lean_obj_tag(v_pre_2082_) {
                    0 => {
                        let mut v_str_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2086_: u8 = 0;
                        v_str_2083_ = leanh::lean_ctor_get(v_x_2080_, 1);
                        v_str_2084_ = leanh::lean_ctor_get(v_pre_2081_, 1);
                        v___x_2085_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__0;
                        v___x_2086_ = lean_string_dec_eq(v_str_2084_, v___x_2085_);
                        if v___x_2086_ == 0 {
                            let mut v___x_2087_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2088_: u8 = 0;
                            v___x_2087_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__1;
                            v___x_2088_ = lean_string_dec_eq(v_str_2084_, v___x_2087_);
                            if v___x_2088_ == 0 {
                                return v___y_2078_;
                            } else {
                                let mut v___x_2089_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2090_: u8 = 0;
                                v___x_2089_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__2;
                                v___x_2090_ = lean_string_dec_eq(v_str_2083_, v___x_2089_);
                                if v___x_2090_ == 0 {
                                    return v___y_2078_;
                                } else {
                                    return v_suppressElabErrors_2079_;
                                }
                            }
                        } else {
                            let mut v___x_2091_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2092_: u8 = 0;
                            v___x_2091_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__3;
                            v___x_2092_ = lean_string_dec_eq(v_str_2083_, v___x_2091_);
                            if v___x_2092_ == 0 {
                                return v___y_2078_;
                            } else {
                                return v_suppressElabErrors_2079_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2093_ = leanh::lean_ctor_get(v_pre_2082_, 0);
                        if leanh::lean_obj_tag(v_pre_2093_) == 0 {
                            let mut v_str_2094_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2095_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2096_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2097_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2098_: u8 = 0;
                            v_str_2094_ = leanh::lean_ctor_get(v_x_2080_, 1);
                            v_str_2095_ = leanh::lean_ctor_get(v_pre_2081_, 1);
                            v_str_2096_ = leanh::lean_ctor_get(v_pre_2082_, 1);
                            v___x_2097_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__4;
                            v___x_2098_ = lean_string_dec_eq(v_str_2096_, v___x_2097_);
                            if v___x_2098_ == 0 {
                                return v___y_2078_;
                            } else {
                                let mut v___x_2099_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2100_: u8 = 0;
                                v___x_2099_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__5;
                                v___x_2100_ = lean_string_dec_eq(v_str_2095_, v___x_2099_);
                                if v___x_2100_ == 0 {
                                    return v___y_2078_;
                                } else {
                                    let mut v___x_2101_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2102_: u8 = 0;
                                    v___x_2101_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___closed__6;
                                    v___x_2102_ = lean_string_dec_eq(v_str_2094_, v___x_2101_);
                                    if v___x_2102_ == 0 {
                                        return v___y_2078_;
                                    } else {
                                        return v_suppressElabErrors_2079_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2078_;
                        }
                    }
                    _ => {
                        return v___y_2078_;
                    }
                }
            }
            0 => {
                let mut v_str_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2105_: u8 = 0;
                v_str_2103_ = leanh::lean_ctor_get(v_x_2080_, 1);
                v___x_2104_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__13;
                v___x_2105_ = lean_string_dec_eq(v_str_2103_, v___x_2104_);
                if v___x_2105_ == 0 {
                    return v___y_2078_;
                } else {
                    return v_suppressElabErrors_2079_;
                }
            }
            _ => {
                return v___y_2078_;
            }
        }
    } else {
        return v___y_2078_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___boxed(
    mut v___y_2106_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_2107_: *mut leanh::LeanObject,
    mut v_x_2108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_9247__boxed_2109_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2110_: u8 = 0;
    let mut v_res_2111_: u8 = 0;
    let mut v_r_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_9247__boxed_2109_ = (leanh::lean_unbox(v___y_2106_) as u8);
    v_suppressElabErrors_boxed_2110_ = (leanh::lean_unbox(v_suppressElabErrors_2107_) as u8);
    v_res_2111_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0(v___y_9247__boxed_2109_, v_suppressElabErrors_boxed_2110_, v_x_2108_);
    leanh::lean_dec(v_x_2108_);
    v_r_2112_ = leanh::lean_box((v_res_2111_) as usize);
    return v_r_2112_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__5(
    mut v_opts_2113_: *mut leanh::LeanObject,
    mut v_opt_2114_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2115_ = leanh::lean_ctor_get(v_opt_2114_, 0);
    v_defValue_2116_ = leanh::lean_ctor_get(v_opt_2114_, 1);
    v_map_2117_ = leanh::lean_ctor_get(v_opts_2113_, 0);
    v___x_2118_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2117_,
            v_name_2115_,
        );
    if leanh::lean_obj_tag(v___x_2118_) == 0 {
        let mut v___x_2119_: u8 = 0;
        v___x_2119_ = (leanh::lean_unbox(v_defValue_2116_) as u8);
        return v___x_2119_;
    } else {
        let mut v_val_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2120_ = leanh::lean_ctor_get(v___x_2118_, 0);
        leanh::lean_inc(v_val_2120_);
        leanh::lean_dec_ref_known(v___x_2118_, 1);
        if leanh::lean_obj_tag(v_val_2120_) == 1 {
            let mut v_v_2121_: u8 = 0;
            v_v_2121_ = leanh::lean_ctor_get_uint8(v_val_2120_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2120_, 0);
            return v_v_2121_;
        } else {
            let mut v___x_2122_: u8 = 0;
            leanh::lean_dec(v_val_2120_);
            v___x_2122_ = (leanh::lean_unbox(v_defValue_2116_) as u8);
            return v___x_2122_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_opts_2123_: *mut leanh::LeanObject,
    mut v_opt_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2125_: u8 = 0;
    let mut v_r_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2125_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__5(v_opts_2123_, v_opt_2124_);
    leanh::lean_dec_ref(v_opt_2124_);
    leanh::lean_dec_ref(v_opts_2123_);
    v_r_2126_ = leanh::lean_box((v_res_2125_) as usize);
    return v_r_2126_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3(
    mut v_ref_2127_: *mut leanh::LeanObject,
    mut v_msgData_2128_: *mut leanh::LeanObject,
    mut v_severity_2129_: u8,
    mut v_isSilent_2130_: u8,
    mut v___y_2131_: *mut leanh::LeanObject,
    mut v___y_2132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2135_: u8 = 0;
    let mut v___y_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2139_: u8 = 0;
    let mut v___y_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2169_: u8 = 0;
    let mut v___y_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: u8 = 0;
    let mut v___y_2174_: u8 = 0;
    let mut v___y_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: u8 = 0;
    let mut v___y_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2184_: u8 = 0;
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut v___y_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: u8 = 0;
    let mut v___y_2199_: u8 = 0;
    let mut v___y_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2202_: u8 = 0;
    let mut v___y_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2209_: u8 = 0;
    let mut v___y_2210_: u8 = 0;
    let mut v___y_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2213_: u8 = 0;
    let mut v_ref_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v___y_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2221_: u8 = 0;
    let mut v___y_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2225_: u8 = 0;
    let mut v___y_2226_: u8 = 0;
    let mut v___y_2228_: u8 = 0;
    let mut v_fileName_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2233_: u8 = 0;
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2218_ = 2;
                v___x_2243_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2129_, v___x_2218_);
                if v___x_2243_ == 0 {
                    v___y_2228_ = v___x_2243_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_2128_);
                    v___x_2244_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2128_);
                    v___y_2228_ = v___x_2244_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2144_ = lean_st_ref_take(v___y_2143_);
                v_currNamespace_2145_ = leanh::lean_ctor_get(v___y_2142_, 6);
                v_openDecls_2146_ = leanh::lean_ctor_get(v___y_2142_, 7);
                v_env_2147_ = leanh::lean_ctor_get(v___x_2144_, 0);
                v_nextMacroScope_2148_ = leanh::lean_ctor_get(v___x_2144_, 1);
                v_ngen_2149_ = leanh::lean_ctor_get(v___x_2144_, 2);
                v_auxDeclNGen_2150_ = leanh::lean_ctor_get(v___x_2144_, 3);
                v_traceState_2151_ = leanh::lean_ctor_get(v___x_2144_, 4);
                v_cache_2152_ = leanh::lean_ctor_get(v___x_2144_, 5);
                v_messages_2153_ = leanh::lean_ctor_get(v___x_2144_, 6);
                v_infoState_2154_ = leanh::lean_ctor_get(v___x_2144_, 7);
                v_snapshotTasks_2155_ = leanh::lean_ctor_get(v___x_2144_, 8);
                v_isSharedCheck_2169_ = (!leanh::lean_is_exclusive(v___x_2144_)) as u8;
                if v_isSharedCheck_2169_ == 0 {
                    v___x_2157_ = v___x_2144_;
                    v_isShared_2158_ = v_isSharedCheck_2169_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2155_);
                    leanh::lean_inc(v_infoState_2154_);
                    leanh::lean_inc(v_messages_2153_);
                    leanh::lean_inc(v_cache_2152_);
                    leanh::lean_inc(v_traceState_2151_);
                    leanh::lean_inc(v_auxDeclNGen_2150_);
                    leanh::lean_inc(v_ngen_2149_);
                    leanh::lean_inc(v_nextMacroScope_2148_);
                    leanh::lean_inc(v_env_2147_);
                    leanh::lean_dec(v___x_2144_);
                    v___x_2157_ = leanh::lean_box(0);
                    v_isShared_2158_ = v_isSharedCheck_2169_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_2146_);
                leanh::lean_inc(v_currNamespace_2145_);
                v___x_2159_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2159_, 0, v_currNamespace_2145_);
                leanh::lean_ctor_set(v___x_2159_, 1, v_openDecls_2146_);
                v___x_2160_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2160_, 0, v___x_2159_);
                leanh::lean_ctor_set(v___x_2160_, 1, v___y_2137_);
                leanh::lean_inc_ref(v___y_2138_);
                leanh::lean_inc_ref(v___y_2136_);
                v___x_2161_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2161_, 0, v___y_2136_);
                leanh::lean_ctor_set(v___x_2161_, 1, v___y_2140_);
                leanh::lean_ctor_set(v___x_2161_, 2, v___y_2141_);
                leanh::lean_ctor_set(v___x_2161_, 3, v___y_2138_);
                leanh::lean_ctor_set(v___x_2161_, 4, v___x_2160_);
                leanh::lean_ctor_set_uint8(
                    v___x_2161_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_2135_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2161_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2139_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2161_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2130_,
                );
                v___x_2162_ = l_Lean_MessageLog_add(v___x_2161_, v_messages_2153_);
                if v_isShared_2158_ == 0 {
                    leanh::lean_ctor_set(v___x_2157_, 6, v___x_2162_);
                    v___x_2164_ = v___x_2157_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_env_2147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_nextMacroScope_2148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_ngen_2149_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 3, v_auxDeclNGen_2150_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 4, v_traceState_2151_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 5, v_cache_2152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 6, v___x_2162_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 7, v_infoState_2154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 8, v_snapshotTasks_2155_);
                    v___x_2164_ = v_reuseFailAlloc_2168_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2165_ = lean_st_ref_set(v___y_2143_, v___x_2164_);
                v___x_2166_ = leanh::lean_box(0);
                v___x_2167_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2167_, 0, v___x_2166_);
                return v___x_2167_;
            }
            4 => {
                v___x_2179_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2128_,
                    );
                v___x_2180_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0(v___x_2179_, v___y_2131_, v___y_2132_);
                v_a_2181_ = leanh::lean_ctor_get(v___x_2180_, 0);
                v_isSharedCheck_2194_ = (!leanh::lean_is_exclusive(v___x_2180_)) as u8;
                if v_isSharedCheck_2194_ == 0 {
                    v___x_2183_ = v___x_2180_;
                    v_isShared_2184_ = v_isSharedCheck_2194_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2181_);
                    leanh::lean_dec(v___x_2180_);
                    v___x_2183_ = leanh::lean_box(0);
                    v_isShared_2184_ = v_isSharedCheck_2194_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_2172_, 2);
                v___x_2185_ = l_Lean_FileMap_toPosition(v___y_2172_, v___y_2176_);
                leanh::lean_dec(v___y_2176_);
                v___x_2186_ = l_Lean_FileMap_toPosition(v___y_2172_, v___y_2178_);
                leanh::lean_dec(v___y_2178_);
                v___x_2187_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2187_, 0, v___x_2186_);
                v___x_2188_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__1;
                if v___y_2173_ == 0 {
                    leanh::lean_del_object(v___x_2183_);
                    leanh::lean_dec_ref(v___y_2171_);
                    v___y_2135_ = v___y_2174_;
                    v___y_2136_ = v___y_2175_;
                    v___y_2137_ = v_a_2181_;
                    v___y_2138_ = v___x_2188_;
                    v___y_2139_ = v___y_2177_;
                    v___y_2140_ = v___x_2185_;
                    v___y_2141_ = v___x_2187_;
                    v___y_2142_ = v___y_2131_;
                    v___y_2143_ = v___y_2132_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2181_);
                    v___x_2189_ = l_Lean_MessageData_hasTag(v___y_2171_, v_a_2181_);
                    if v___x_2189_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2187_, 1);
                        leanh::lean_dec_ref(v___x_2185_);
                        leanh::lean_dec(v_a_2181_);
                        v___x_2190_ = leanh::lean_box(0);
                        if v_isShared_2184_ == 0 {
                            leanh::lean_ctor_set(v___x_2183_, 0, v___x_2190_);
                            v___x_2192_ = v___x_2183_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2193_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
                            v___x_2192_ = v_reuseFailAlloc_2193_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2183_);
                        v___y_2135_ = v___y_2174_;
                        v___y_2136_ = v___y_2175_;
                        v___y_2137_ = v_a_2181_;
                        v___y_2138_ = v___x_2188_;
                        v___y_2139_ = v___y_2177_;
                        v___y_2140_ = v___x_2185_;
                        v___y_2141_ = v___x_2187_;
                        v___y_2142_ = v___y_2131_;
                        v___y_2143_ = v___y_2132_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2192_;
            }
            7 => {
                v___x_2204_ = l_Lean_Syntax_getTailPos_x3f(v___y_2201_, v___y_2198_);
                leanh::lean_dec(v___y_2201_);
                if leanh::lean_obj_tag(v___x_2204_) == 0 {
                    leanh::lean_inc(v___y_2203_);
                    v___y_2171_ = v___y_2196_;
                    v___y_2172_ = v___y_2197_;
                    v___y_2173_ = v___y_2199_;
                    v___y_2174_ = v___y_2198_;
                    v___y_2175_ = v___y_2200_;
                    v___y_2176_ = v___y_2203_;
                    v___y_2177_ = v___y_2202_;
                    v___y_2178_ = v___y_2203_;
                    state = 4;
                    continue;
                } else {
                    v_val_2205_ = leanh::lean_ctor_get(v___x_2204_, 0);
                    leanh::lean_inc(v_val_2205_);
                    leanh::lean_dec_ref_known(v___x_2204_, 1);
                    v___y_2171_ = v___y_2196_;
                    v___y_2172_ = v___y_2197_;
                    v___y_2173_ = v___y_2199_;
                    v___y_2174_ = v___y_2198_;
                    v___y_2175_ = v___y_2200_;
                    v___y_2176_ = v___y_2203_;
                    v___y_2177_ = v___y_2202_;
                    v___y_2178_ = v_val_2205_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2214_ = l_Lean_replaceRef(v_ref_2127_, v___y_2212_);
                v___x_2215_ = l_Lean_Syntax_getPos_x3f(v_ref_2214_, v___y_2210_);
                if leanh::lean_obj_tag(v___x_2215_) == 0 {
                    v___x_2216_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2196_ = v___y_2207_;
                    v___y_2197_ = v___y_2208_;
                    v___y_2198_ = v___y_2210_;
                    v___y_2199_ = v___y_2209_;
                    v___y_2200_ = v___y_2211_;
                    v___y_2201_ = v_ref_2214_;
                    v___y_2202_ = v___y_2213_;
                    v___y_2203_ = v___x_2216_;
                    state = 7;
                    continue;
                } else {
                    v_val_2217_ = leanh::lean_ctor_get(v___x_2215_, 0);
                    leanh::lean_inc(v_val_2217_);
                    leanh::lean_dec_ref_known(v___x_2215_, 1);
                    v___y_2196_ = v___y_2207_;
                    v___y_2197_ = v___y_2208_;
                    v___y_2198_ = v___y_2210_;
                    v___y_2199_ = v___y_2209_;
                    v___y_2200_ = v___y_2211_;
                    v___y_2201_ = v_ref_2214_;
                    v___y_2202_ = v___y_2213_;
                    v___y_2203_ = v_val_2217_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2226_ == 0 {
                    v___y_2207_ = v___y_2224_;
                    v___y_2208_ = v___y_2220_;
                    v___y_2209_ = v___y_2221_;
                    v___y_2210_ = v___y_2225_;
                    v___y_2211_ = v___y_2222_;
                    v___y_2212_ = v___y_2223_;
                    v___y_2213_ = v_severity_2129_;
                    state = 8;
                    continue;
                } else {
                    v___y_2207_ = v___y_2224_;
                    v___y_2208_ = v___y_2220_;
                    v___y_2209_ = v___y_2221_;
                    v___y_2210_ = v___y_2225_;
                    v___y_2211_ = v___y_2222_;
                    v___y_2212_ = v___y_2223_;
                    v___y_2213_ = v___x_2218_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2228_ == 0 {
                    v_fileName_2229_ = leanh::lean_ctor_get(v___y_2131_, 0);
                    v_fileMap_2230_ = leanh::lean_ctor_get(v___y_2131_, 1);
                    v_options_2231_ = leanh::lean_ctor_get(v___y_2131_, 2);
                    v_ref_2232_ = leanh::lean_ctor_get(v___y_2131_, 5);
                    v_suppressElabErrors_2233_ = leanh::lean_ctor_get_uint8(
                        v___y_2131_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2234_ = leanh::lean_box((v___y_2228_) as usize);
                    v___x_2235_ = leanh::lean_box((v_suppressElabErrors_2233_) as usize);
                    v___f_2236_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2236_, 0, v___x_2234_);
                    leanh::lean_closure_set(v___f_2236_, 1, v___x_2235_);
                    v___x_2237_ = 1;
                    v___x_2238_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2129_, v___x_2237_);
                    if v___x_2238_ == 0 {
                        v___y_2220_ = v_fileMap_2230_;
                        v___y_2221_ = v_suppressElabErrors_2233_;
                        v___y_2222_ = v_fileName_2229_;
                        v___y_2223_ = v_ref_2232_;
                        v___y_2224_ = v___f_2236_;
                        v___y_2225_ = v___y_2228_;
                        v___y_2226_ = v___x_2238_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2239_ = l_Lean_warningAsError;
                        v___x_2240_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__5(v_options_2231_, v___x_2239_);
                        v___y_2220_ = v_fileMap_2230_;
                        v___y_2221_ = v_suppressElabErrors_2233_;
                        v___y_2222_ = v_fileName_2229_;
                        v___y_2223_ = v_ref_2232_;
                        v___y_2224_ = v___f_2236_;
                        v___y_2225_ = v___y_2228_;
                        v___y_2226_ = v___x_2240_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2128_);
                    v___x_2241_ = leanh::lean_box(0);
                    v___x_2242_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2242_, 0, v___x_2241_);
                    return v___x_2242_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(
    mut v_ref_2245_: *mut leanh::LeanObject,
    mut v_msgData_2246_: *mut leanh::LeanObject,
    mut v_severity_2247_: *mut leanh::LeanObject,
    mut v_isSilent_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
    mut v___y_2251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2252_: u8 = 0;
    let mut v_isSilent_boxed_2253_: u8 = 0;
    let mut v_res_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2252_ = (leanh::lean_unbox(v_severity_2247_) as u8);
    v_isSilent_boxed_2253_ = (leanh::lean_unbox(v_isSilent_2248_) as u8);
    v_res_2254_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_ref_2245_, v_msgData_2246_, v_severity_boxed_2252_, v_isSilent_boxed_2253_, v___y_2249_, v___y_2250_);
    leanh::lean_dec(v___y_2250_);
    leanh::lean_dec_ref(v___y_2249_);
    leanh::lean_dec(v_ref_2245_);
    return v_res_2254_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2(
    mut v_msgData_2255_: *mut leanh::LeanObject,
    mut v_severity_2256_: u8,
    mut v_isSilent_2257_: u8,
    mut v___y_2258_: *mut leanh::LeanObject,
    mut v___y_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2261_ = leanh::lean_ctor_get(v___y_2258_, 5);
    v___x_2262_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_ref_2261_, v_msgData_2255_, v_severity_2256_, v_isSilent_2257_, v___y_2258_, v___y_2259_);
    return v___x_2262_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_msgData_2263_: *mut leanh::LeanObject,
    mut v_severity_2264_: *mut leanh::LeanObject,
    mut v_isSilent_2265_: *mut leanh::LeanObject,
    mut v___y_2266_: *mut leanh::LeanObject,
    mut v___y_2267_: *mut leanh::LeanObject,
    mut v___y_2268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2269_: u8 = 0;
    let mut v_isSilent_boxed_2270_: u8 = 0;
    let mut v_res_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2269_ = (leanh::lean_unbox(v_severity_2264_) as u8);
    v_isSilent_boxed_2270_ = (leanh::lean_unbox(v_isSilent_2265_) as u8);
    v_res_2271_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2263_, v_severity_boxed_2269_, v_isSilent_boxed_2270_, v___y_2266_, v___y_2267_);
    leanh::lean_dec(v___y_2267_);
    leanh::lean_dec_ref(v___y_2266_);
    return v_res_2271_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1(
    mut v_msgData_2272_: *mut leanh::LeanObject,
    mut v___y_2273_: *mut leanh::LeanObject,
    mut v___y_2274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2276_: u8 = 0;
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = 1;
    v___x_2277_ = 0;
    v___x_2278_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2(v_msgData_2272_, v___x_2276_, v___x_2277_, v___y_2273_, v___y_2274_);
    return v___x_2278_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1___boxed(
    mut v_msgData_2279_: *mut leanh::LeanObject,
    mut v___y_2280_: *mut leanh::LeanObject,
    mut v___y_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2283_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1(v_msgData_2279_, v___y_2280_, v___y_2281_);
    leanh::lean_dec(v___y_2281_);
    leanh::lean_dec_ref(v___y_2280_);
    return v_res_2283_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_2284_: *mut leanh::LeanObject,
    mut v___y_2285_: *mut leanh::LeanObject,
    mut v___y_2286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2288_ = leanh::lean_ctor_get(v___y_2285_, 5);
                v___x_2289_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0_spec__0(v_msg_2284_, v___y_2285_, v___y_2286_);
                v_a_2290_ = leanh::lean_ctor_get(v___x_2289_, 0);
                v_isSharedCheck_2298_ = (!leanh::lean_is_exclusive(v___x_2289_)) as u8;
                if v_isSharedCheck_2298_ == 0 {
                    v___x_2292_ = v___x_2289_;
                    v_isShared_2293_ = v_isSharedCheck_2298_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2290_);
                    leanh::lean_dec(v___x_2289_);
                    v___x_2292_ = leanh::lean_box(0);
                    v_isShared_2293_ = v_isSharedCheck_2298_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2288_);
                v___x_2294_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2294_, 0, v_ref_2288_);
                leanh::lean_ctor_set(v___x_2294_, 1, v_a_2290_);
                if v_isShared_2293_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2292_, 1);
                    leanh::lean_ctor_set(v___x_2292_, 0, v___x_2294_);
                    v___x_2296_ = v___x_2292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2297_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
                    v___x_2296_ = v_reuseFailAlloc_2297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_2299_: *mut leanh::LeanObject,
    mut v___y_2300_: *mut leanh::LeanObject,
    mut v___y_2301_: *mut leanh::LeanObject,
    mut v___y_2302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2303_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0___redArg(v_msg_2299_, v___y_2300_, v___y_2301_);
    leanh::lean_dec(v___y_2301_);
    leanh::lean_dec_ref(v___y_2300_);
    return v_res_2303_;
}
pub unsafe fn _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2307_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_;
    v___x_2308_ = l_Lean_MessageData_ofFormat(v___x_2307_);
    return v___x_2308_;
}
pub unsafe fn _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2312_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_;
    v___x_2313_ = l_Lean_MessageData_ofFormat(v___x_2312_);
    return v___x_2313_;
}
pub unsafe fn _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2315_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_;
    v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
    return v___x_2316_;
}
pub unsafe fn l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_(
    mut v___x_2317_: *mut leanh::LeanObject,
    mut v___x_2318_: *mut leanh::LeanObject,
    mut v_x_2319_: *mut leanh::LeanObject,
    mut v_stx_2320_: *mut leanh::LeanObject,
    mut v___y_2321_: *mut leanh::LeanObject,
    mut v___y_2322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: u8 = 0;
    let mut v___y_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2343_: u8 = 0;
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2347_: u8 = 0;
    let mut v___y_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2364_: u8 = 0;
    let mut v___y_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v___y_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2393_: u8 = 0;
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2398_: u8 = 0;
    let mut v___y_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_since_x3f_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: u8 = 0;
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2416_: u8 = 0;
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2420_: u8 = 0;
    let mut v_a_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2424_: u8 = 0;
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2428_: u8 = 0;
    let mut v___y_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: u8 = 0;
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: u8 = 0;
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_since_x3f_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2455_: u8 = 0;
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: u8 = 0;
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2330_ = l_Lean_Name_mkStr2(v___x_2317_, v___x_2318_);
                leanh::lean_inc(v_stx_2320_);
                v___x_2331_ = l_Lean_Syntax_isOfKind(v_stx_2320_, v___x_2330_);
                leanh::lean_dec(v___x_2330_);
                if v___x_2331_ == 0 {
                    leanh::lean_dec(v_stx_2320_);
                    v___x_2444_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_);
                    v___x_2445_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0___redArg(v___x_2444_, v___y_2321_, v___y_2322_);
                    return v___x_2445_;
                } else {
                    v___x_2446_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2447_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2461_ = l_Lean_Syntax_getArg(v_stx_2320_, v___x_2447_);
                    v___x_2462_ = l_Lean_Syntax_isNone(v___x_2461_);
                    if v___x_2462_ == 0 {
                        leanh::lean_inc(v___x_2461_);
                        v___x_2463_ = l_Lean_Syntax_matchesNull(v___x_2461_, v___x_2447_);
                        if v___x_2463_ == 0 {
                            leanh::lean_dec(v___x_2461_);
                            leanh::lean_dec(v_stx_2320_);
                            v___x_2464_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_);
                            v___x_2465_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0___redArg(v___x_2464_, v___y_2321_, v___y_2322_);
                            return v___x_2465_;
                        } else {
                            v_id_x3f_2466_ = l_Lean_Syntax_getArg(v___x_2461_, v___x_2446_);
                            leanh::lean_dec(v___x_2461_);
                            v___x_2467_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2467_, 0, v_id_x3f_2466_);
                            v_id_x3f_2449_ = v___x_2467_;
                            v___y_2450_ = v___y_2321_;
                            v___y_2451_ = v___y_2322_;
                            state = 20;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2461_);
                        v___x_2468_ = leanh::lean_box(0);
                        v_id_x3f_2449_ = v___x_2468_;
                        v___y_2450_ = v___y_2321_;
                        v___y_2451_ = v___y_2322_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2328_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2328_, 0, v___y_2325_);
                leanh::lean_ctor_set(v___x_2328_, 1, v___y_2326_);
                leanh::lean_ctor_set(v___x_2328_, 2, v___y_2327_);
                v___x_2329_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2329_, 0, v___x_2328_);
                return v___x_2329_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_2335_) == 0 {
                    if v___x_2331_ == 0 {
                        v___y_2325_ = v___y_2333_;
                        v___y_2326_ = v___y_2334_;
                        v___y_2327_ = v___y_2335_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2338_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_);
                        v___x_2339_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1(v___x_2338_, v___y_2336_, v___y_2337_);
                        if leanh::lean_obj_tag(v___x_2339_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2339_, 1);
                            v___y_2325_ = v___y_2333_;
                            v___y_2326_ = v___y_2334_;
                            v___y_2327_ = v___y_2335_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___y_2334_);
                            leanh::lean_dec(v___y_2333_);
                            v_a_2340_ = leanh::lean_ctor_get(v___x_2339_, 0);
                            v_isSharedCheck_2347_ =
                                (!leanh::lean_is_exclusive(v___x_2339_)) as u8;
                            if v_isSharedCheck_2347_ == 0 {
                                v___x_2342_ = v___x_2339_;
                                v_isShared_2343_ = v_isSharedCheck_2347_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2340_);
                                leanh::lean_dec(v___x_2339_);
                                v___x_2342_ = leanh::lean_box(0);
                                v_isShared_2343_ = v_isSharedCheck_2347_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___y_2325_ = v___y_2333_;
                    v___y_2326_ = v___y_2334_;
                    v___y_2327_ = v___y_2335_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2343_ == 0 {
                    v___x_2345_ = v___x_2342_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2346_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
                    v___x_2345_ = v_reuseFailAlloc_2346_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2345_;
            }
            5 => {
                if leanh::lean_obj_tag(v___y_2352_) == 0 {
                    if v___x_2331_ == 0 {
                        v___y_2333_ = v___y_2349_;
                        v___y_2334_ = v___y_2350_;
                        v___y_2335_ = v___y_2354_;
                        v___y_2336_ = v___y_2353_;
                        v___y_2337_ = v___y_2351_;
                        state = 2;
                        continue;
                    } else {
                        if leanh::lean_obj_tag(v___y_2350_) == 0 {
                            v___x_2355_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_);
                            v___x_2356_ = l_Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1(v___x_2355_, v___y_2353_, v___y_2351_);
                            if leanh::lean_obj_tag(v___x_2356_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2356_, 1);
                                v___y_2333_ = v___y_2349_;
                                v___y_2334_ = v___y_2350_;
                                v___y_2335_ = v___y_2354_;
                                v___y_2336_ = v___y_2353_;
                                v___y_2337_ = v___y_2351_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___y_2354_);
                                leanh::lean_dec(v___y_2349_);
                                v_a_2357_ = leanh::lean_ctor_get(v___x_2356_, 0);
                                v_isSharedCheck_2364_ =
                                    (!leanh::lean_is_exclusive(v___x_2356_)) as u8;
                                if v_isSharedCheck_2364_ == 0 {
                                    v___x_2359_ = v___x_2356_;
                                    v_isShared_2360_ = v_isSharedCheck_2364_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2357_);
                                    leanh::lean_dec(v___x_2356_);
                                    v___x_2359_ = leanh::lean_box(0);
                                    v_isShared_2360_ = v_isSharedCheck_2364_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            v___y_2333_ = v___y_2349_;
                            v___y_2334_ = v___y_2350_;
                            v___y_2335_ = v___y_2354_;
                            v___y_2336_ = v___y_2353_;
                            v___y_2337_ = v___y_2351_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v___y_2352_, 1);
                    v___y_2333_ = v___y_2349_;
                    v___y_2334_ = v___y_2350_;
                    v___y_2335_ = v___y_2354_;
                    v___y_2336_ = v___y_2353_;
                    v___y_2337_ = v___y_2351_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_2360_ == 0 {
                    v___x_2362_ = v___x_2359_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2363_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
                    v___x_2362_ = v_reuseFailAlloc_2363_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2362_;
            }
            8 => {
                if leanh::lean_obj_tag(v___y_2367_) == 0 {
                    v___x_2372_ = leanh::lean_box(0);
                    v___y_2349_ = v___y_2366_;
                    v___y_2350_ = v___y_2371_;
                    v___y_2351_ = v___y_2368_;
                    v___y_2352_ = v___y_2369_;
                    v___y_2353_ = v___y_2370_;
                    v___y_2354_ = v___x_2372_;
                    state = 5;
                    continue;
                } else {
                    v_val_2373_ = leanh::lean_ctor_get(v___y_2367_, 0);
                    v_isSharedCheck_2381_ = (!leanh::lean_is_exclusive(v___y_2367_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v___x_2375_ = v___y_2367_;
                        v_isShared_2376_ = v_isSharedCheck_2381_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2373_);
                        leanh::lean_dec(v___y_2367_);
                        v___x_2375_ = leanh::lean_box(0);
                        v_isShared_2376_ = v_isSharedCheck_2381_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2377_ = l_Lean_TSyntax_getString(v_val_2373_);
                leanh::lean_dec(v_val_2373_);
                if v_isShared_2376_ == 0 {
                    leanh::lean_ctor_set(v___x_2375_, 0, v___x_2377_);
                    v___x_2379_ = v___x_2375_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
                    v___x_2379_ = v_reuseFailAlloc_2380_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_2349_ = v___y_2366_;
                v___y_2350_ = v___y_2371_;
                v___y_2351_ = v___y_2368_;
                v___y_2352_ = v___y_2369_;
                v___y_2353_ = v___y_2370_;
                v___y_2354_ = v___x_2379_;
                state = 5;
                continue;
            }
            11 => {
                if leanh::lean_obj_tag(v___y_2384_) == 0 {
                    v___x_2389_ = leanh::lean_box(0);
                    v___y_2366_ = v___y_2383_;
                    v___y_2367_ = v___y_2385_;
                    v___y_2368_ = v___y_2388_;
                    v___y_2369_ = v___y_2386_;
                    v___y_2370_ = v___y_2387_;
                    v___y_2371_ = v___x_2389_;
                    state = 8;
                    continue;
                } else {
                    v_val_2390_ = leanh::lean_ctor_get(v___y_2384_, 0);
                    v_isSharedCheck_2398_ = (!leanh::lean_is_exclusive(v___y_2384_)) as u8;
                    if v_isSharedCheck_2398_ == 0 {
                        v___x_2392_ = v___y_2384_;
                        v_isShared_2393_ = v_isSharedCheck_2398_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2390_);
                        leanh::lean_dec(v___y_2384_);
                        v___x_2392_ = leanh::lean_box(0);
                        v_isShared_2393_ = v_isSharedCheck_2398_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                v___x_2394_ = l_Lean_TSyntax_getString(v_val_2390_);
                leanh::lean_dec(v_val_2390_);
                if v_isShared_2393_ == 0 {
                    leanh::lean_ctor_set(v___x_2392_, 0, v___x_2394_);
                    v___x_2396_ = v___x_2392_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2397_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
                    v___x_2396_ = v_reuseFailAlloc_2397_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_2366_ = v___y_2383_;
                v___y_2367_ = v___y_2385_;
                v___y_2368_ = v___y_2388_;
                v___y_2369_ = v___y_2386_;
                v___y_2370_ = v___y_2387_;
                v___y_2371_ = v___x_2396_;
                state = 8;
                continue;
            }
            14 => {
                if leanh::lean_obj_tag(v___y_2401_) == 0 {
                    v___x_2405_ = leanh::lean_box(0);
                    v___y_2383_ = v___x_2405_;
                    v___y_2384_ = v___y_2400_;
                    v___y_2385_ = v_since_x3f_2402_;
                    v___y_2386_ = v___y_2401_;
                    v___y_2387_ = v___y_2403_;
                    v___y_2388_ = v___y_2404_;
                    state = 11;
                    continue;
                } else {
                    v_val_2406_ = leanh::lean_ctor_get(v___y_2401_, 0);
                    v___x_2407_ = leanh::lean_box(0);
                    leanh::lean_inc(v_val_2406_);
                    v___x_2408_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_val_2406_,
                        v___x_2407_,
                        v___y_2403_,
                        v___y_2404_,
                    );
                    if leanh::lean_obj_tag(v___x_2408_) == 0 {
                        v_a_2409_ = leanh::lean_ctor_get(v___x_2408_, 0);
                        leanh::lean_inc_n(v_a_2409_, 2);
                        leanh::lean_dec_ref_known(v___x_2408_, 1);
                        v___x_2410_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2410_, 0, v_a_2409_);
                        v___x_2411_ = 0;
                        v___x_2412_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2(v_a_2409_, v___x_2411_, v___y_2403_, v___y_2404_);
                        if leanh::lean_obj_tag(v___x_2412_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2412_, 1);
                            v___y_2383_ = v___x_2410_;
                            v___y_2384_ = v___y_2400_;
                            v___y_2385_ = v_since_x3f_2402_;
                            v___y_2386_ = v___y_2401_;
                            v___y_2387_ = v___y_2403_;
                            v___y_2388_ = v___y_2404_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v___x_2410_, 1);
                            leanh::lean_dec_ref_known(v___y_2401_, 1);
                            leanh::lean_dec(v_since_x3f_2402_);
                            leanh::lean_dec(v___y_2400_);
                            v_a_2413_ = leanh::lean_ctor_get(v___x_2412_, 0);
                            v_isSharedCheck_2420_ =
                                (!leanh::lean_is_exclusive(v___x_2412_)) as u8;
                            if v_isSharedCheck_2420_ == 0 {
                                v___x_2415_ = v___x_2412_;
                                v_isShared_2416_ = v_isSharedCheck_2420_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2413_);
                                leanh::lean_dec(v___x_2412_);
                                v___x_2415_ = leanh::lean_box(0);
                                v_isShared_2416_ = v_isSharedCheck_2420_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_2401_, 1);
                        leanh::lean_dec(v_since_x3f_2402_);
                        leanh::lean_dec(v___y_2400_);
                        v_a_2421_ = leanh::lean_ctor_get(v___x_2408_, 0);
                        v_isSharedCheck_2428_ =
                            (!leanh::lean_is_exclusive(v___x_2408_)) as u8;
                        if v_isSharedCheck_2428_ == 0 {
                            v___x_2423_ = v___x_2408_;
                            v_isShared_2424_ = v_isSharedCheck_2428_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2421_);
                            leanh::lean_dec(v___x_2408_);
                            v___x_2423_ = leanh::lean_box(0);
                            v_isShared_2424_ = v_isSharedCheck_2428_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            15 => {
                if v_isShared_2416_ == 0 {
                    v___x_2418_ = v___x_2415_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2419_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
                    v___x_2418_ = v_reuseFailAlloc_2419_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2418_;
            }
            17 => {
                if v_isShared_2424_ == 0 {
                    v___x_2426_ = v___x_2423_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
                    v___x_2426_ = v_reuseFailAlloc_2427_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2426_;
            }
            19 => {
                v___x_2434_ = leanh::lean_unsigned_to_nat(3);
                v___x_2435_ = l_Lean_Syntax_getArg(v_stx_2320_, v___x_2434_);
                leanh::lean_dec(v_stx_2320_);
                v___x_2436_ = l_Lean_Syntax_isNone(v___x_2435_);
                if v___x_2436_ == 0 {
                    v___x_2437_ = leanh::lean_unsigned_to_nat(5);
                    leanh::lean_inc(v___x_2435_);
                    v___x_2438_ = l_Lean_Syntax_matchesNull(v___x_2435_, v___x_2437_);
                    if v___x_2438_ == 0 {
                        leanh::lean_dec(v___x_2435_);
                        leanh::lean_dec(v_text_x3f_2431_);
                        leanh::lean_dec(v___y_2430_);
                        v___x_2439_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_);
                        v___x_2440_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0___redArg(v___x_2439_, v___y_2432_, v___y_2433_);
                        return v___x_2440_;
                    } else {
                        v_since_x3f_2441_ = l_Lean_Syntax_getArg(v___x_2435_, v___x_2434_);
                        leanh::lean_dec(v___x_2435_);
                        v___x_2442_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2442_, 0, v_since_x3f_2441_);
                        v___y_2400_ = v_text_x3f_2431_;
                        v___y_2401_ = v___y_2430_;
                        v_since_x3f_2402_ = v___x_2442_;
                        v___y_2403_ = v___y_2432_;
                        v___y_2404_ = v___y_2433_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2435_);
                    v___x_2443_ = leanh::lean_box(0);
                    v___y_2400_ = v_text_x3f_2431_;
                    v___y_2401_ = v___y_2430_;
                    v_since_x3f_2402_ = v___x_2443_;
                    v___y_2403_ = v___y_2432_;
                    v___y_2404_ = v___y_2433_;
                    state = 14;
                    continue;
                }
            }
            20 => {
                v___x_2452_ = leanh::lean_unsigned_to_nat(2);
                v___x_2453_ = l_Lean_Syntax_getArg(v_stx_2320_, v___x_2452_);
                v___x_2454_ = l_Lean_Syntax_isNone(v___x_2453_);
                if v___x_2454_ == 0 {
                    leanh::lean_inc(v___x_2453_);
                    v___x_2455_ = l_Lean_Syntax_matchesNull(v___x_2453_, v___x_2447_);
                    if v___x_2455_ == 0 {
                        leanh::lean_dec(v___x_2453_);
                        leanh::lean_dec(v_id_x3f_2449_);
                        leanh::lean_dec(v_stx_2320_);
                        v___x_2456_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__once), _init_l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_);
                        v___x_2457_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0___redArg(v___x_2456_, v___y_2450_, v___y_2451_);
                        return v___x_2457_;
                    } else {
                        v_text_x3f_2458_ = l_Lean_Syntax_getArg(v___x_2453_, v___x_2446_);
                        leanh::lean_dec(v___x_2453_);
                        v___x_2459_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2459_, 0, v_text_x3f_2458_);
                        v___y_2430_ = v_id_x3f_2449_;
                        v_text_x3f_2431_ = v___x_2459_;
                        v___y_2432_ = v___y_2450_;
                        v___y_2433_ = v___y_2451_;
                        state = 19;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2453_);
                    v___x_2460_ = leanh::lean_box(0);
                    v___y_2430_ = v_id_x3f_2449_;
                    v_text_x3f_2431_ = v___x_2460_;
                    v___y_2432_ = v___y_2450_;
                    v___y_2433_ = v___y_2451_;
                    state = 19;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2____boxed(
    mut v___x_2469_: *mut leanh::LeanObject,
    mut v___x_2470_: *mut leanh::LeanObject,
    mut v_x_2471_: *mut leanh::LeanObject,
    mut v_stx_2472_: *mut leanh::LeanObject,
    mut v___y_2473_: *mut leanh::LeanObject,
    mut v___y_2474_: *mut leanh::LeanObject,
    mut v___y_2475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2476_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_(v___x_2469_, v___x_2470_, v_x_2471_, v_stx_2472_, v___y_2473_, v___y_2474_);
    leanh::lean_dec(v___y_2474_);
    leanh::lean_dec_ref(v___y_2473_);
    leanh::lean_dec(v_x_2471_);
    return v_res_2476_;
}
pub unsafe fn l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_(
    mut v___x_2477_: u8,
    mut v_env_2478_: *mut leanh::LeanObject,
    mut v_n_2479_: *mut leanh::LeanObject,
    mut v_x_2480_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2481_: u8 = 0;
    v___x_2481_ = l_Lean_Environment_contains(v_env_2478_, v_n_2479_, v___x_2477_);
    return v___x_2481_;
}
pub unsafe fn l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2____boxed(
    mut v___x_2482_: *mut leanh::LeanObject,
    mut v_env_2483_: *mut leanh::LeanObject,
    mut v_n_2484_: *mut leanh::LeanObject,
    mut v_x_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9933__boxed_2486_: u8 = 0;
    let mut v_res_2487_: u8 = 0;
    let mut v_r_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9933__boxed_2486_ = (leanh::lean_unbox(v___x_2482_) as u8);
    v_res_2487_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_(v___x_9933__boxed_2486_, v_env_2483_, v_n_2484_, v_x_2485_);
    leanh::lean_dec_ref(v_x_2485_);
    v_r_2488_ = leanh::lean_box((v_res_2487_) as usize);
    return v_r_2488_;
}
pub unsafe fn l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_;
    v___x_2517_ = l_Lean_registerParametricAttribute___redArg(v___x_2516_);
    return v___x_2517_;
}
pub unsafe fn l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2____boxed(
    mut v_a_2518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2519_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_();
    return v_res_2519_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_2520_: *mut leanh::LeanObject,
    mut v_msg_2521_: *mut leanh::LeanObject,
    mut v___y_2522_: *mut leanh::LeanObject,
    mut v___y_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2525_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0___redArg(v_msg_2521_, v___y_2522_, v___y_2523_);
    return v___x_2525_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_2526_: *mut leanh::LeanObject,
    mut v_msg_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2531_ = l_Lean_throwError___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__0(v_00_u03b1_2526_, v_msg_2527_, v___y_2528_, v___y_2529_);
    leanh::lean_dec(v___y_2529_);
    leanh::lean_dec_ref(v___y_2528_);
    return v_res_2531_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6(
    mut v_00_u03b2_2532_: *mut leanh::LeanObject,
    mut v_m_2533_: *mut leanh::LeanObject,
    mut v_a_2534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___redArg(v_m_2533_, v_a_2534_);
    return v___x_2535_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6___boxed(
    mut v_00_u03b2_2536_: *mut leanh::LeanObject,
    mut v_m_2537_: *mut leanh::LeanObject,
    mut v_a_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6(v_00_u03b2_2536_, v_m_2537_, v_a_2538_);
    leanh::lean_dec(v_a_2538_);
    leanh::lean_dec_ref(v_m_2537_);
    return v_res_2539_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6(
    mut v_00_u03b2_2540_: *mut leanh::LeanObject,
    mut v_x_2541_: *mut leanh::LeanObject,
    mut v_x_2542_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2543_: u8 = 0;
    v___x_2543_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6___redArg(v_x_2541_, v_x_2542_);
    return v___x_2543_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b2_2544_: *mut leanh::LeanObject,
    mut v_x_2545_: *mut leanh::LeanObject,
    mut v_x_2546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2547_: u8 = 0;
    let mut v_r_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2547_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6(v_00_u03b2_2544_, v_x_2545_, v_x_2546_);
    leanh::lean_dec_ref(v_x_2546_);
    leanh::lean_dec_ref(v_x_2545_);
    v_r_2548_ = leanh::lean_box((v_res_2547_) as usize);
    return v_r_2548_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6_spec__10(
    mut v_00_u03b2_2549_: *mut leanh::LeanObject,
    mut v_a_2550_: *mut leanh::LeanObject,
    mut v_x_2551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2552_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6_spec__10___redArg(v_a_2550_, v_x_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6_spec__10___boxed(
    mut v_00_u03b2_2553_: *mut leanh::LeanObject,
    mut v_a_2554_: *mut leanh::LeanObject,
    mut v_x_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__6_spec__10(v_00_u03b2_2553_, v_a_2554_, v_x_2555_);
    leanh::lean_dec(v_x_2555_);
    leanh::lean_dec(v_a_2554_);
    return v_res_2556_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8(
    mut v_00_u03b2_2557_: *mut leanh::LeanObject,
    mut v_x_2558_: *mut leanh::LeanObject,
    mut v_x_2559_: usize,
    mut v_x_2560_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2561_: u8 = 0;
    v___x_2561_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___redArg(v_x_2558_, v_x_2559_, v_x_2560_);
    return v___x_2561_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b2_2562_: *mut leanh::LeanObject,
    mut v_x_2563_: *mut leanh::LeanObject,
    mut v_x_2564_: *mut leanh::LeanObject,
    mut v_x_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_10055__boxed_2566_: usize = 0;
    let mut v_res_2567_: u8 = 0;
    let mut v_r_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_10055__boxed_2566_ = leanh::lean_unbox_usize(v_x_2564_);
    leanh::lean_dec(v_x_2564_);
    v_res_2567_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8(v_00_u03b2_2562_, v_x_2563_, v_x_10055__boxed_2566_, v_x_2565_);
    leanh::lean_dec_ref(v_x_2565_);
    leanh::lean_dec_ref(v_x_2563_);
    v_r_2568_ = leanh::lean_box((v_res_2567_) as usize);
    return v_r_2568_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8_spec__11(
    mut v_00_u03b2_2569_: *mut leanh::LeanObject,
    mut v_keys_2570_: *mut leanh::LeanObject,
    mut v_vals_2571_: *mut leanh::LeanObject,
    mut v_heq_2572_: *mut leanh::LeanObject,
    mut v_i_2573_: *mut leanh::LeanObject,
    mut v_k_2574_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2575_: u8 = 0;
    v___x_2575_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8_spec__11___redArg(v_keys_2570_, v_i_2573_, v_k_2574_);
    return v___x_2575_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8_spec__11___boxed(
    mut v_00_u03b2_2576_: *mut leanh::LeanObject,
    mut v_keys_2577_: *mut leanh::LeanObject,
    mut v_vals_2578_: *mut leanh::LeanObject,
    mut v_heq_2579_: *mut leanh::LeanObject,
    mut v_i_2580_: *mut leanh::LeanObject,
    mut v_k_2581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2582_: u8 = 0;
    let mut v_r_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2582_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__6_spec__8_spec__11(v_00_u03b2_2576_, v_keys_2577_, v_vals_2578_, v_heq_2579_, v_i_2580_, v_k_2581_);
    leanh::lean_dec_ref(v_k_2581_);
    leanh::lean_dec_ref(v_vals_2578_);
    leanh::lean_dec_ref(v_keys_2577_);
    v_r_2583_ = leanh::lean_box((v_res_2582_) as usize);
    return v_r_2583_;
}
pub unsafe fn l_Lean_Linter_setDeprecated___redArg___lam__0(
    mut v_declName_2584_: *mut leanh::LeanObject,
    mut v_entry_2585_: *mut leanh::LeanObject,
    mut v_inst_2586_: *mut leanh::LeanObject,
    mut v_inst_2587_: *mut leanh::LeanObject,
    mut v_inst_2588_: *mut leanh::LeanObject,
    mut v_env_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut v_a_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2590_ = l_Lean_Linter_deprecatedAttr;
                v___x_2591_ = l_Lean_ParametricAttribute_setParam___redArg(
                    v___x_2590_,
                    v_env_2589_,
                    v_declName_2584_,
                    v_entry_2585_,
                );
                if leanh::lean_obj_tag(v___x_2591_) == 0 {
                    leanh::lean_dec_ref(v_inst_2588_);
                    v_a_2592_ = leanh::lean_ctor_get(v___x_2591_, 0);
                    v_isSharedCheck_2601_ = (!leanh::lean_is_exclusive(v___x_2591_)) as u8;
                    if v_isSharedCheck_2601_ == 0 {
                        v___x_2594_ = v___x_2591_;
                        v_isShared_2595_ = v_isSharedCheck_2601_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2592_);
                        leanh::lean_dec(v___x_2591_);
                        v___x_2594_ = leanh::lean_box(0);
                        v_isShared_2595_ = v_isSharedCheck_2601_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_2587_);
                    leanh::lean_dec_ref(v_inst_2586_);
                    v_a_2602_ = leanh::lean_ctor_get(v___x_2591_, 0);
                    leanh::lean_inc(v_a_2602_);
                    leanh::lean_dec_ref_known(v___x_2591_, 1);
                    v___x_2603_ = l_Lean_setEnv___redArg(v_inst_2588_, v_a_2602_);
                    return v___x_2603_;
                }
            }
            1 => {
                if v_isShared_2595_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2594_, 3);
                    v___x_2597_ = v___x_2594_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2600_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2592_);
                    v___x_2597_ = v_reuseFailAlloc_2600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2598_ = l_Lean_MessageData_ofFormat(v___x_2597_);
                v___x_2599_ = l_Lean_throwError___redArg(v_inst_2586_, v_inst_2587_, v___x_2598_);
                return v___x_2599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_setDeprecated___redArg(
    mut v_inst_2604_: *mut leanh::LeanObject,
    mut v_inst_2605_: *mut leanh::LeanObject,
    mut v_inst_2606_: *mut leanh::LeanObject,
    mut v_declName_2607_: *mut leanh::LeanObject,
    mut v_entry_2608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2609_ = leanh::lean_ctor_get(v_inst_2604_, 1);
    leanh::lean_inc(v_toBind_2609_);
    v_getEnv_2610_ = leanh::lean_ctor_get(v_inst_2605_, 0);
    leanh::lean_inc(v_getEnv_2610_);
    v___f_2611_ = leanh::lean_alloc_closure(
        l_Lean_Linter_setDeprecated___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_2611_, 0, v_declName_2607_);
    leanh::lean_closure_set(v___f_2611_, 1, v_entry_2608_);
    leanh::lean_closure_set(v___f_2611_, 2, v_inst_2604_);
    leanh::lean_closure_set(v___f_2611_, 3, v_inst_2606_);
    leanh::lean_closure_set(v___f_2611_, 4, v_inst_2605_);
    v___x_2612_ = leanh::lean_apply_4(
        v_toBind_2609_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_2610_,
        v___f_2611_,
    );
    return v___x_2612_;
}
pub unsafe fn l_Lean_Linter_setDeprecated(
    mut v_m_2613_: *mut leanh::LeanObject,
    mut v_inst_2614_: *mut leanh::LeanObject,
    mut v_inst_2615_: *mut leanh::LeanObject,
    mut v_inst_2616_: *mut leanh::LeanObject,
    mut v_declName_2617_: *mut leanh::LeanObject,
    mut v_entry_2618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2619_ = l_Lean_Linter_setDeprecated___redArg(
        v_inst_2614_,
        v_inst_2615_,
        v_inst_2616_,
        v_declName_2617_,
        v_entry_2618_,
    );
    return v___x_2619_;
}
pub unsafe fn l_Lean_Linter_isDeprecated(
    mut v_env_2620_: *mut leanh::LeanObject,
    mut v_declName_2621_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2622_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
    v___x_2623_ = l_Lean_Linter_deprecatedAttr;
    v___x_2624_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_2622_,
        v___x_2623_,
        v_env_2620_,
        v_declName_2621_,
    );
    if leanh::lean_obj_tag(v___x_2624_) == 0 {
        let mut v___x_2625_: u8 = 0;
        v___x_2625_ = 0;
        return v___x_2625_;
    } else {
        let mut v___x_2626_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_2624_, 1);
        v___x_2626_ = 1;
        return v___x_2626_;
    }
}
pub unsafe fn l_Lean_Linter_isDeprecated___boxed(
    mut v_env_2627_: *mut leanh::LeanObject,
    mut v_declName_2628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2629_: u8 = 0;
    let mut v_r_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2629_ = l_Lean_Linter_isDeprecated(v_env_2627_, v_declName_2628_);
    v_r_2630_ = leanh::lean_box((v_res_2629_) as usize);
    return v_r_2630_;
}
pub unsafe fn l_Lean_MessageData_isDeprecationWarning___lam__0(
    mut v_x_2631_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: u8 = 0;
    v___x_2632_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_;
    v___x_2633_ = lean_name_eq(v_x_2631_, v___x_2632_);
    return v___x_2633_;
}
pub unsafe fn l_Lean_MessageData_isDeprecationWarning___lam__0___boxed(
    mut v_x_2634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2635_: u8 = 0;
    let mut v_r_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2635_ = l_Lean_MessageData_isDeprecationWarning___lam__0(v_x_2634_);
    leanh::lean_dec(v_x_2634_);
    v_r_2636_ = leanh::lean_box((v_res_2635_) as usize);
    return v_r_2636_;
}
pub unsafe fn l_Lean_MessageData_isDeprecationWarning(
    mut v_msg_2638_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: u8 = 0;
    v___f_2639_ = l_Lean_MessageData_isDeprecationWarning___closed__0;
    v___x_2640_ = l_Lean_MessageData_hasTag(v___f_2639_, v_msg_2638_);
    return v___x_2640_;
}
pub unsafe fn l_Lean_MessageData_isDeprecationWarning___boxed(
    mut v_msg_2641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2642_: u8 = 0;
    let mut v_r_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2642_ = l_Lean_MessageData_isDeprecationWarning(v_msg_2641_);
    v_r_2643_ = leanh::lean_box((v_res_2642_) as usize);
    return v_r_2643_;
}
pub unsafe fn l_Lean_Linter_getDeprecatedNewName(
    mut v_env_2644_: *mut leanh::LeanObject,
    mut v_declName_2645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2646_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
    v___x_2647_ = l_Lean_Linter_deprecatedAttr;
    v___x_2648_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_2646_,
        v___x_2647_,
        v_env_2644_,
        v_declName_2645_,
    );
    if leanh::lean_obj_tag(v___x_2648_) == 0 {
        let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2649_ = leanh::lean_box(0);
        return v___x_2649_;
    } else {
        let mut v_val_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_newName_x3f_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2650_ = leanh::lean_ctor_get(v___x_2648_, 0);
        leanh::lean_inc(v_val_2650_);
        leanh::lean_dec_ref_known(v___x_2648_, 1);
        v_newName_x3f_2651_ = leanh::lean_ctor_get(v_val_2650_, 0);
        leanh::lean_inc(v_newName_x3f_2651_);
        leanh::lean_dec(v_val_2650_);
        return v_newName_x3f_2651_;
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3_spec__4(
    mut v_msgData_2652_: *mut leanh::LeanObject,
    mut v___y_2653_: *mut leanh::LeanObject,
    mut v___y_2654_: *mut leanh::LeanObject,
    mut v___y_2655_: *mut leanh::LeanObject,
    mut v___y_2656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2658_ = lean_st_ref_get(v___y_2656_);
    v_env_2659_ = leanh::lean_ctor_get(v___x_2658_, 0);
    leanh::lean_inc_ref(v_env_2659_);
    leanh::lean_dec(v___x_2658_);
    v___x_2660_ = lean_st_ref_get(v___y_2654_);
    v_mctx_2661_ = leanh::lean_ctor_get(v___x_2660_, 0);
    leanh::lean_inc_ref(v_mctx_2661_);
    leanh::lean_dec(v___x_2660_);
    v_lctx_2662_ = leanh::lean_ctor_get(v___y_2653_, 2);
    v_options_2663_ = leanh::lean_ctor_get(v___y_2655_, 2);
    leanh::lean_inc_ref(v_options_2663_);
    leanh::lean_inc_ref(v_lctx_2662_);
    v___x_2664_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2664_, 0, v_env_2659_);
    leanh::lean_ctor_set(v___x_2664_, 1, v_mctx_2661_);
    leanh::lean_ctor_set(v___x_2664_, 2, v_lctx_2662_);
    leanh::lean_ctor_set(v___x_2664_, 3, v_options_2663_);
    v___x_2665_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2665_, 0, v___x_2664_);
    leanh::lean_ctor_set(v___x_2665_, 1, v_msgData_2652_);
    v___x_2666_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2666_, 0, v___x_2665_);
    return v___x_2666_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msgData_2667_: *mut leanh::LeanObject,
    mut v___y_2668_: *mut leanh::LeanObject,
    mut v___y_2669_: *mut leanh::LeanObject,
    mut v___y_2670_: *mut leanh::LeanObject,
    mut v___y_2671_: *mut leanh::LeanObject,
    mut v___y_2672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2673_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3_spec__4(v_msgData_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
    leanh::lean_dec(v___y_2671_);
    leanh::lean_dec_ref(v___y_2670_);
    leanh::lean_dec(v___y_2669_);
    leanh::lean_dec_ref(v___y_2668_);
    return v_res_2673_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3(
    mut v_ref_2674_: *mut leanh::LeanObject,
    mut v_msgData_2675_: *mut leanh::LeanObject,
    mut v_severity_2676_: u8,
    mut v_isSilent_2677_: u8,
    mut v___y_2678_: *mut leanh::LeanObject,
    mut v___y_2679_: *mut leanh::LeanObject,
    mut v___y_2680_: *mut leanh::LeanObject,
    mut v___y_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2688_: u8 = 0;
    let mut v___y_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2690_: u8 = 0;
    let mut v___y_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2707_: u8 = 0;
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2718_: u8 = 0;
    let mut v___y_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2722_: u8 = 0;
    let mut v___y_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: u8 = 0;
    let mut v___y_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2726_: u8 = 0;
    let mut v___y_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: u8 = 0;
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2743_: u8 = 0;
    let mut v___y_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2749_: u8 = 0;
    let mut v___y_2750_: u8 = 0;
    let mut v___y_2751_: u8 = 0;
    let mut v___y_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: u8 = 0;
    let mut v___y_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2761_: u8 = 0;
    let mut v___y_2762_: u8 = 0;
    let mut v_ref_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: u8 = 0;
    let mut v___y_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2773_: u8 = 0;
    let mut v___y_2774_: u8 = 0;
    let mut v___y_2775_: u8 = 0;
    let mut v___y_2777_: u8 = 0;
    let mut v_fileName_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2782_: u8 = 0;
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: u8 = 0;
    let mut v___x_2787_: u8 = 0;
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: u8 = 0;
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: u8 = 0;
    let mut v___x_2793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2767_ = 2;
                v___x_2792_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2676_, v___x_2767_);
                if v___x_2792_ == 0 {
                    v___y_2777_ = v___x_2792_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_2675_);
                    v___x_2793_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2675_);
                    v___y_2777_ = v___x_2793_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2693_ = lean_st_ref_take(v___y_2692_);
                v_currNamespace_2694_ = leanh::lean_ctor_get(v___y_2691_, 6);
                v_openDecls_2695_ = leanh::lean_ctor_get(v___y_2691_, 7);
                v_env_2696_ = leanh::lean_ctor_get(v___x_2693_, 0);
                v_nextMacroScope_2697_ = leanh::lean_ctor_get(v___x_2693_, 1);
                v_ngen_2698_ = leanh::lean_ctor_get(v___x_2693_, 2);
                v_auxDeclNGen_2699_ = leanh::lean_ctor_get(v___x_2693_, 3);
                v_traceState_2700_ = leanh::lean_ctor_get(v___x_2693_, 4);
                v_cache_2701_ = leanh::lean_ctor_get(v___x_2693_, 5);
                v_messages_2702_ = leanh::lean_ctor_get(v___x_2693_, 6);
                v_infoState_2703_ = leanh::lean_ctor_get(v___x_2693_, 7);
                v_snapshotTasks_2704_ = leanh::lean_ctor_get(v___x_2693_, 8);
                v_isSharedCheck_2718_ = (!leanh::lean_is_exclusive(v___x_2693_)) as u8;
                if v_isSharedCheck_2718_ == 0 {
                    v___x_2706_ = v___x_2693_;
                    v_isShared_2707_ = v_isSharedCheck_2718_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2704_);
                    leanh::lean_inc(v_infoState_2703_);
                    leanh::lean_inc(v_messages_2702_);
                    leanh::lean_inc(v_cache_2701_);
                    leanh::lean_inc(v_traceState_2700_);
                    leanh::lean_inc(v_auxDeclNGen_2699_);
                    leanh::lean_inc(v_ngen_2698_);
                    leanh::lean_inc(v_nextMacroScope_2697_);
                    leanh::lean_inc(v_env_2696_);
                    leanh::lean_dec(v___x_2693_);
                    v___x_2706_ = leanh::lean_box(0);
                    v_isShared_2707_ = v_isSharedCheck_2718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_2695_);
                leanh::lean_inc(v_currNamespace_2694_);
                v___x_2708_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2708_, 0, v_currNamespace_2694_);
                leanh::lean_ctor_set(v___x_2708_, 1, v_openDecls_2695_);
                v___x_2709_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2709_, 0, v___x_2708_);
                leanh::lean_ctor_set(v___x_2709_, 1, v___y_2685_);
                leanh::lean_inc_ref(v___y_2687_);
                leanh::lean_inc_ref(v___y_2684_);
                v___x_2710_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2710_, 0, v___y_2684_);
                leanh::lean_ctor_set(v___x_2710_, 1, v___y_2686_);
                leanh::lean_ctor_set(v___x_2710_, 2, v___y_2689_);
                leanh::lean_ctor_set(v___x_2710_, 3, v___y_2687_);
                leanh::lean_ctor_set(v___x_2710_, 4, v___x_2709_);
                leanh::lean_ctor_set_uint8(
                    v___x_2710_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_2690_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2710_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2688_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2710_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2677_,
                );
                v___x_2711_ = l_Lean_MessageLog_add(v___x_2710_, v_messages_2702_);
                if v_isShared_2707_ == 0 {
                    leanh::lean_ctor_set(v___x_2706_, 6, v___x_2711_);
                    v___x_2713_ = v___x_2706_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2717_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_env_2696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_nextMacroScope_2697_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 2, v_ngen_2698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 3, v_auxDeclNGen_2699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 4, v_traceState_2700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 5, v_cache_2701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 6, v___x_2711_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 7, v_infoState_2703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 8, v_snapshotTasks_2704_);
                    v___x_2713_ = v_reuseFailAlloc_2717_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2714_ = lean_st_ref_set(v___y_2692_, v___x_2713_);
                v___x_2715_ = leanh::lean_box(0);
                v___x_2716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2716_, 0, v___x_2715_);
                return v___x_2716_;
            }
            4 => {
                v___x_2728_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2675_,
                    );
                v___x_2729_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3_spec__4(v___x_2728_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
                v_a_2730_ = leanh::lean_ctor_get(v___x_2729_, 0);
                v_isSharedCheck_2743_ = (!leanh::lean_is_exclusive(v___x_2729_)) as u8;
                if v_isSharedCheck_2743_ == 0 {
                    v___x_2732_ = v___x_2729_;
                    v_isShared_2733_ = v_isSharedCheck_2743_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2730_);
                    leanh::lean_dec(v___x_2729_);
                    v___x_2732_ = leanh::lean_box(0);
                    v_isShared_2733_ = v_isSharedCheck_2743_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_2723_, 2);
                v___x_2734_ = l_Lean_FileMap_toPosition(v___y_2723_, v___y_2725_);
                leanh::lean_dec(v___y_2725_);
                v___x_2735_ = l_Lean_FileMap_toPosition(v___y_2723_, v___y_2727_);
                leanh::lean_dec(v___y_2727_);
                v___x_2736_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2736_, 0, v___x_2735_);
                v___x_2737_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4_spec__7___closed__1;
                if v___y_2724_ == 0 {
                    leanh::lean_del_object(v___x_2732_);
                    leanh::lean_dec_ref(v___y_2720_);
                    v___y_2684_ = v___y_2721_;
                    v___y_2685_ = v_a_2730_;
                    v___y_2686_ = v___x_2734_;
                    v___y_2687_ = v___x_2737_;
                    v___y_2688_ = v___y_2722_;
                    v___y_2689_ = v___x_2736_;
                    v___y_2690_ = v___y_2726_;
                    v___y_2691_ = v___y_2680_;
                    v___y_2692_ = v___y_2681_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2730_);
                    v___x_2738_ = l_Lean_MessageData_hasTag(v___y_2720_, v_a_2730_);
                    if v___x_2738_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2736_, 1);
                        leanh::lean_dec_ref(v___x_2734_);
                        leanh::lean_dec(v_a_2730_);
                        v___x_2739_ = leanh::lean_box(0);
                        if v_isShared_2733_ == 0 {
                            leanh::lean_ctor_set(v___x_2732_, 0, v___x_2739_);
                            v___x_2741_ = v___x_2732_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2742_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
                            v___x_2741_ = v_reuseFailAlloc_2742_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2732_);
                        v___y_2684_ = v___y_2721_;
                        v___y_2685_ = v_a_2730_;
                        v___y_2686_ = v___x_2734_;
                        v___y_2687_ = v___x_2737_;
                        v___y_2688_ = v___y_2722_;
                        v___y_2689_ = v___x_2736_;
                        v___y_2690_ = v___y_2726_;
                        v___y_2691_ = v___y_2680_;
                        v___y_2692_ = v___y_2681_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2741_;
            }
            7 => {
                v___x_2753_ = l_Lean_Syntax_getTailPos_x3f(v___y_2746_, v___y_2751_);
                leanh::lean_dec(v___y_2746_);
                if leanh::lean_obj_tag(v___x_2753_) == 0 {
                    leanh::lean_inc(v___y_2752_);
                    v___y_2720_ = v___y_2745_;
                    v___y_2721_ = v___y_2747_;
                    v___y_2722_ = v___y_2749_;
                    v___y_2723_ = v___y_2748_;
                    v___y_2724_ = v___y_2750_;
                    v___y_2725_ = v___y_2752_;
                    v___y_2726_ = v___y_2751_;
                    v___y_2727_ = v___y_2752_;
                    state = 4;
                    continue;
                } else {
                    v_val_2754_ = leanh::lean_ctor_get(v___x_2753_, 0);
                    leanh::lean_inc(v_val_2754_);
                    leanh::lean_dec_ref_known(v___x_2753_, 1);
                    v___y_2720_ = v___y_2745_;
                    v___y_2721_ = v___y_2747_;
                    v___y_2722_ = v___y_2749_;
                    v___y_2723_ = v___y_2748_;
                    v___y_2724_ = v___y_2750_;
                    v___y_2725_ = v___y_2752_;
                    v___y_2726_ = v___y_2751_;
                    v___y_2727_ = v_val_2754_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2763_ = l_Lean_replaceRef(v_ref_2674_, v___y_2760_);
                v___x_2764_ = l_Lean_Syntax_getPos_x3f(v_ref_2763_, v___y_2761_);
                if leanh::lean_obj_tag(v___x_2764_) == 0 {
                    v___x_2765_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2745_ = v___y_2756_;
                    v___y_2746_ = v_ref_2763_;
                    v___y_2747_ = v___y_2757_;
                    v___y_2748_ = v___y_2758_;
                    v___y_2749_ = v___y_2762_;
                    v___y_2750_ = v___y_2759_;
                    v___y_2751_ = v___y_2761_;
                    v___y_2752_ = v___x_2765_;
                    state = 7;
                    continue;
                } else {
                    v_val_2766_ = leanh::lean_ctor_get(v___x_2764_, 0);
                    leanh::lean_inc(v_val_2766_);
                    leanh::lean_dec_ref_known(v___x_2764_, 1);
                    v___y_2745_ = v___y_2756_;
                    v___y_2746_ = v_ref_2763_;
                    v___y_2747_ = v___y_2757_;
                    v___y_2748_ = v___y_2758_;
                    v___y_2749_ = v___y_2762_;
                    v___y_2750_ = v___y_2759_;
                    v___y_2751_ = v___y_2761_;
                    v___y_2752_ = v_val_2766_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2775_ == 0 {
                    v___y_2756_ = v___y_2769_;
                    v___y_2757_ = v___y_2770_;
                    v___y_2758_ = v___y_2771_;
                    v___y_2759_ = v___y_2773_;
                    v___y_2760_ = v___y_2772_;
                    v___y_2761_ = v___y_2774_;
                    v___y_2762_ = v_severity_2676_;
                    state = 8;
                    continue;
                } else {
                    v___y_2756_ = v___y_2769_;
                    v___y_2757_ = v___y_2770_;
                    v___y_2758_ = v___y_2771_;
                    v___y_2759_ = v___y_2773_;
                    v___y_2760_ = v___y_2772_;
                    v___y_2761_ = v___y_2774_;
                    v___y_2762_ = v___x_2767_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2777_ == 0 {
                    v_fileName_2778_ = leanh::lean_ctor_get(v___y_2680_, 0);
                    v_fileMap_2779_ = leanh::lean_ctor_get(v___y_2680_, 1);
                    v_options_2780_ = leanh::lean_ctor_get(v___y_2680_, 2);
                    v_ref_2781_ = leanh::lean_ctor_get(v___y_2680_, 5);
                    v_suppressElabErrors_2782_ = leanh::lean_ctor_get_uint8(
                        v___y_2680_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2783_ = leanh::lean_box((v___y_2777_) as usize);
                    v___x_2784_ = leanh::lean_box((v_suppressElabErrors_2782_) as usize);
                    v___f_2785_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2785_, 0, v___x_2783_);
                    leanh::lean_closure_set(v___f_2785_, 1, v___x_2784_);
                    v___x_2786_ = 1;
                    v___x_2787_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2676_, v___x_2786_);
                    if v___x_2787_ == 0 {
                        v___y_2769_ = v___f_2785_;
                        v___y_2770_ = v_fileName_2778_;
                        v___y_2771_ = v_fileMap_2779_;
                        v___y_2772_ = v_ref_2781_;
                        v___y_2773_ = v_suppressElabErrors_2782_;
                        v___y_2774_ = v___y_2777_;
                        v___y_2775_ = v___x_2787_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2788_ = l_Lean_warningAsError;
                        v___x_2789_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__1_spec__2_spec__3_spec__5(v_options_2780_, v___x_2788_);
                        v___y_2769_ = v___f_2785_;
                        v___y_2770_ = v_fileName_2778_;
                        v___y_2771_ = v_fileMap_2779_;
                        v___y_2772_ = v_ref_2781_;
                        v___y_2773_ = v_suppressElabErrors_2782_;
                        v___y_2774_ = v___y_2777_;
                        v___y_2775_ = v___x_2789_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2675_);
                    v___x_2790_ = leanh::lean_box(0);
                    v___x_2791_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2791_, 0, v___x_2790_);
                    return v___x_2791_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3___boxed(
    mut v_ref_2794_: *mut leanh::LeanObject,
    mut v_msgData_2795_: *mut leanh::LeanObject,
    mut v_severity_2796_: *mut leanh::LeanObject,
    mut v_isSilent_2797_: *mut leanh::LeanObject,
    mut v___y_2798_: *mut leanh::LeanObject,
    mut v___y_2799_: *mut leanh::LeanObject,
    mut v___y_2800_: *mut leanh::LeanObject,
    mut v___y_2801_: *mut leanh::LeanObject,
    mut v___y_2802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2803_: u8 = 0;
    let mut v_isSilent_boxed_2804_: u8 = 0;
    let mut v_res_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2803_ = (leanh::lean_unbox(v_severity_2796_) as u8);
    v_isSilent_boxed_2804_ = (leanh::lean_unbox(v_isSilent_2797_) as u8);
    v_res_2805_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3(v_ref_2794_, v_msgData_2795_, v_severity_boxed_2803_, v_isSilent_boxed_2804_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
    leanh::lean_dec(v___y_2801_);
    leanh::lean_dec_ref(v___y_2800_);
    leanh::lean_dec(v___y_2799_);
    leanh::lean_dec_ref(v___y_2798_);
    leanh::lean_dec(v_ref_2794_);
    return v_res_2805_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2(
    mut v_msgData_2806_: *mut leanh::LeanObject,
    mut v_severity_2807_: u8,
    mut v_isSilent_2808_: u8,
    mut v___y_2809_: *mut leanh::LeanObject,
    mut v___y_2810_: *mut leanh::LeanObject,
    mut v___y_2811_: *mut leanh::LeanObject,
    mut v___y_2812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2814_ = leanh::lean_ctor_get(v___y_2811_, 5);
    v___x_2815_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2_spec__3(v_ref_2814_, v_msgData_2806_, v_severity_2807_, v_isSilent_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
    return v___x_2815_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2___boxed(
    mut v_msgData_2816_: *mut leanh::LeanObject,
    mut v_severity_2817_: *mut leanh::LeanObject,
    mut v_isSilent_2818_: *mut leanh::LeanObject,
    mut v___y_2819_: *mut leanh::LeanObject,
    mut v___y_2820_: *mut leanh::LeanObject,
    mut v___y_2821_: *mut leanh::LeanObject,
    mut v___y_2822_: *mut leanh::LeanObject,
    mut v___y_2823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2824_: u8 = 0;
    let mut v_isSilent_boxed_2825_: u8 = 0;
    let mut v_res_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2824_ = (leanh::lean_unbox(v_severity_2817_) as u8);
    v_isSilent_boxed_2825_ = (leanh::lean_unbox(v_isSilent_2818_) as u8);
    v_res_2826_ =
        l_Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2(
            v_msgData_2816_,
            v_severity_boxed_2824_,
            v_isSilent_boxed_2825_,
            v___y_2819_,
            v___y_2820_,
            v___y_2821_,
            v___y_2822_,
        );
    leanh::lean_dec(v___y_2822_);
    leanh::lean_dec_ref(v___y_2821_);
    leanh::lean_dec(v___y_2820_);
    leanh::lean_dec_ref(v___y_2819_);
    return v_res_2826_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1(
    mut v_msgData_2827_: *mut leanh::LeanObject,
    mut v___y_2828_: *mut leanh::LeanObject,
    mut v___y_2829_: *mut leanh::LeanObject,
    mut v___y_2830_: *mut leanh::LeanObject,
    mut v___y_2831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2833_: u8 = 0;
    let mut v___x_2834_: u8 = 0;
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2833_ = 1;
    v___x_2834_ = 0;
    v___x_2835_ =
        l_Lean_log___at___00Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1_spec__2(
            v_msgData_2827_,
            v___x_2833_,
            v___x_2834_,
            v___y_2828_,
            v___y_2829_,
            v___y_2830_,
            v___y_2831_,
        );
    return v___x_2835_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1___boxed(
    mut v_msgData_2836_: *mut leanh::LeanObject,
    mut v___y_2837_: *mut leanh::LeanObject,
    mut v___y_2838_: *mut leanh::LeanObject,
    mut v___y_2839_: *mut leanh::LeanObject,
    mut v___y_2840_: *mut leanh::LeanObject,
    mut v___y_2841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2842_ = l_Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1(
        v_msgData_2836_,
        v___y_2837_,
        v___y_2838_,
        v___y_2839_,
        v___y_2840_,
    );
    leanh::lean_dec(v___y_2840_);
    leanh::lean_dec_ref(v___y_2839_);
    leanh::lean_dec(v___y_2838_);
    leanh::lean_dec_ref(v___y_2837_);
    return v_res_2842_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(
    mut v_o_2843_: *mut leanh::LeanObject,
    mut v___y_2844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2846_ = lean_st_ref_get(v___y_2844_);
    v_env_2847_ = leanh::lean_ctor_get(v___x_2846_, 0);
    leanh::lean_inc_ref(v_env_2847_);
    leanh::lean_dec(v___x_2846_);
    v___x_2848_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_2849_ = leanh::lean_ctor_get(v___x_2848_, 0);
    v_asyncMode_2850_ = leanh::lean_ctor_get(v_toEnvExtension_2849_, 2);
    v___x_2851_ = leanh::lean_box(1);
    v___x_2852_ = leanh::lean_box(0);
    v_linterSets_2853_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2851_,
        v___x_2848_,
        v_env_2847_,
        v_asyncMode_2850_,
        v___x_2852_,
    );
    v___x_2854_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2854_, 0, v_o_2843_);
    leanh::lean_ctor_set(v___x_2854_, 1, v_linterSets_2853_);
    v___x_2855_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2855_, 0, v___x_2854_);
    return v___x_2855_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg___boxed(
    mut v_o_2856_: *mut leanh::LeanObject,
    mut v___y_2857_: *mut leanh::LeanObject,
    mut v___y_2858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2859_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_2856_, v___y_2857_);
    leanh::lean_dec(v___y_2857_);
    return v_res_2859_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(
    mut v___y_2860_: *mut leanh::LeanObject,
    mut v___y_2861_: *mut leanh::LeanObject,
    mut v___y_2862_: *mut leanh::LeanObject,
    mut v___y_2863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_options_2865_ = leanh::lean_ctor_get(v___y_2862_, 2);
    leanh::lean_inc_ref(v_options_2865_);
    v___x_2866_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_options_2865_, v___y_2863_);
    return v___x_2866_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0___boxed(
    mut v___y_2867_: *mut leanh::LeanObject,
    mut v___y_2868_: *mut leanh::LeanObject,
    mut v___y_2869_: *mut leanh::LeanObject,
    mut v___y_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2872_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(
        v___y_2867_,
        v___y_2868_,
        v___y_2869_,
        v___y_2870_,
    );
    leanh::lean_dec(v___y_2870_);
    leanh::lean_dec_ref(v___y_2869_);
    leanh::lean_dec(v___y_2868_);
    leanh::lean_dec_ref(v___y_2867_);
    return v_res_2872_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2874_ = l_Lean_Linter_checkDeprecated___closed__0;
    v___x_2875_ = l_Lean_stringToMessageData(v___x_2874_);
    return v___x_2875_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2877_ = l_Lean_Linter_checkDeprecated___closed__2;
    v___x_2878_ = l_Lean_stringToMessageData(v___x_2877_);
    return v___x_2878_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2880_ = l_Lean_Linter_checkDeprecated___closed__4;
    v___x_2881_ = l_Lean_stringToMessageData(v___x_2880_);
    return v___x_2881_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2883_ = l_Lean_Linter_checkDeprecated___closed__6;
    v___x_2884_ = l_Lean_stringToMessageData(v___x_2883_);
    return v___x_2884_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2886_ = l_Lean_Linter_checkDeprecated___closed__8;
    v___x_2887_ = l_Lean_stringToMessageData(v___x_2886_);
    return v___x_2887_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2889_ = l_Lean_Linter_checkDeprecated___closed__10;
    v___x_2890_ = l_Lean_stringToMessageData(v___x_2889_);
    return v___x_2890_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2892_ = l_Lean_Linter_checkDeprecated___closed__12;
    v___x_2893_ = l_Lean_stringToMessageData(v___x_2892_);
    return v___x_2893_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2895_ = l_Lean_Linter_checkDeprecated___closed__14;
    v___x_2896_ = l_Lean_stringToMessageData(v___x_2895_);
    return v___x_2896_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2898_ = l_Lean_Linter_checkDeprecated___closed__16;
    v___x_2899_ = l_Lean_stringToMessageData(v___x_2898_);
    return v___x_2899_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2902_ = l_Lean_Linter_checkDeprecated___closed__18;
    v___x_2903_ = l_Lean_MessageData_ofFormat(v___x_2902_);
    return v___x_2903_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2905_ = l_Lean_Linter_checkDeprecated___closed__20;
    v___x_2906_ = l_Lean_stringToMessageData(v___x_2905_);
    return v___x_2906_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2908_ = l_Lean_Linter_checkDeprecated___closed__22;
    v___x_2909_ = l_Lean_stringToMessageData(v___x_2908_);
    return v___x_2909_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__25() -> *mut leanh::LeanObject {
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2911_ = l_Lean_Linter_checkDeprecated___closed__24;
    v___x_2912_ = l_Lean_stringToMessageData(v___x_2911_);
    return v___x_2912_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__27() -> *mut leanh::LeanObject {
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = l_Lean_Linter_checkDeprecated___closed__26;
    v___x_2915_ = l_Lean_stringToMessageData(v___x_2914_);
    return v___x_2915_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__29() -> *mut leanh::LeanObject {
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ = l_Lean_Linter_checkDeprecated___closed__28;
    v___x_2918_ = l_Lean_stringToMessageData(v___x_2917_);
    return v___x_2918_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__30() -> u64 {
    let mut v___x_2919_: u8 = 0;
    let mut v___x_2920_: u64 = 0;
    v___x_2919_ = 2;
    v___x_2920_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2919_);
    return v___x_2920_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__32() -> *mut leanh::LeanObject {
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2922_ = l_Lean_Linter_checkDeprecated___closed__31;
    v___x_2923_ = l_Lean_stringToMessageData(v___x_2922_);
    return v___x_2923_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__34() -> *mut leanh::LeanObject {
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2925_ = l_Lean_Linter_checkDeprecated___closed__33;
    v___x_2926_ = l_Lean_stringToMessageData(v___x_2925_);
    return v___x_2926_;
}
pub unsafe fn _init_l_Lean_Linter_checkDeprecated___closed__36() -> *mut leanh::LeanObject {
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2928_ = l_Lean_Linter_checkDeprecated___closed__35;
    v___x_2929_ = l_Lean_stringToMessageData(v___x_2928_);
    return v___x_2929_;
}
pub unsafe fn l_Lean_Linter_checkDeprecated(
    mut v_declName_2930_: *mut leanh::LeanObject,
    mut v_a_2931_: *mut leanh::LeanObject,
    mut v_a_2932_: *mut leanh::LeanObject,
    mut v_a_2933_: *mut leanh::LeanObject,
    mut v_a_2934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: u8 = 0;
    let mut v_extraMsg_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newName_x3f_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: u8 = 0;
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3019_: u8 = 0;
    let mut v___y_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: u8 = 0;
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: u8 = 0;
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: u8 = 0;
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3053_: u8 = 0;
    let mut v_ctxApprox_3054_: u8 = 0;
    let mut v_quasiPatternApprox_3055_: u8 = 0;
    let mut v_constApprox_3056_: u8 = 0;
    let mut v_isDefEqStuckEx_3057_: u8 = 0;
    let mut v_unificationHints_3058_: u8 = 0;
    let mut v_proofIrrelevance_3059_: u8 = 0;
    let mut v_assignSyntheticOpaque_3060_: u8 = 0;
    let mut v_offsetCnstrs_3061_: u8 = 0;
    let mut v_etaStruct_3062_: u8 = 0;
    let mut v_univApprox_3063_: u8 = 0;
    let mut v_iota_3064_: u8 = 0;
    let mut v_beta_3065_: u8 = 0;
    let mut v_proj_3066_: u8 = 0;
    let mut v_zeta_3067_: u8 = 0;
    let mut v_zetaDelta_3068_: u8 = 0;
    let mut v_zetaUnused_3069_: u8 = 0;
    let mut v_zetaHave_3070_: u8 = 0;
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v_trackZetaDelta_3074_: u8 = 0;
    let mut v_zetaDeltaSet_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3081_: u8 = 0;
    let mut v_inTypeClassResolution_3082_: u8 = 0;
    let mut v_cacheInferType_3083_: u8 = 0;
    let mut v___x_3084_: u8 = 0;
    let mut v_config_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u64 = 0;
    let mut v___x_3088_: u64 = 0;
    let mut v___x_3089_: u64 = 0;
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: u64 = 0;
    let mut v___x_3093_: u64 = 0;
    let mut v_key_3094_: u64 = 0;
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_reuseFailAlloc_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_val_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2936_ =
                    l_Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0(
                        v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_,
                    );
                v_a_2937_ = leanh::lean_ctor_get(v___x_2936_, 0);
                v_isSharedCheck_3135_ = (!leanh::lean_is_exclusive(v___x_2936_)) as u8;
                if v_isSharedCheck_3135_ == 0 {
                    v___x_2939_ = v___x_2936_;
                    v_isShared_2940_ = v_isSharedCheck_3135_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2937_);
                    leanh::lean_dec(v___x_2936_);
                    v___x_2939_ = leanh::lean_box(0);
                    v_isShared_2940_ = v_isSharedCheck_3135_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2941_ = l_Lean_Linter_linter_deprecated;
                v___x_2942_ = l_Lean_Linter_getLinterValue(v___x_2941_, v_a_2937_);
                leanh::lean_dec(v_a_2937_);
                if v___x_2942_ == 0 {
                    leanh::lean_dec(v_declName_2930_);
                    v___x_2971_ = leanh::lean_box(0);
                    if v_isShared_2940_ == 0 {
                        leanh::lean_ctor_set(v___x_2939_, 0, v___x_2971_);
                        v___x_2973_ = v___x_2939_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2974_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
                        v___x_2973_ = v_reuseFailAlloc_2974_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2975_ = lean_st_ref_get(v_a_2934_);
                    v_env_2976_ = leanh::lean_ctor_get(v___x_2975_, 0);
                    leanh::lean_inc_ref(v_env_2976_);
                    leanh::lean_dec(v___x_2975_);
                    v___x_2977_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
                    v___x_2978_ = l_Lean_Linter_deprecatedAttr;
                    leanh::lean_inc(v_declName_2930_);
                    v___x_2979_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                        v___x_2977_,
                        v___x_2978_,
                        v_env_2976_,
                        v_declName_2930_,
                    );
                    if leanh::lean_obj_tag(v___x_2979_) == 1 {
                        leanh::lean_del_object(v___x_2939_);
                        v_val_2980_ = leanh::lean_ctor_get(v___x_2979_, 0);
                        leanh::lean_inc(v_val_2980_);
                        leanh::lean_dec_ref_known(v___x_2979_, 1);
                        v_text_x3f_2981_ = leanh::lean_ctor_get(v_val_2980_, 1);
                        if leanh::lean_obj_tag(v_text_x3f_2981_) == 0 {
                            v_newName_x3f_2982_ = leanh::lean_ctor_get(v_val_2980_, 0);
                            leanh::lean_inc(v_newName_x3f_2982_);
                            leanh::lean_dec(v_val_2980_);
                            if leanh::lean_obj_tag(v_newName_x3f_2982_) == 0 {
                                v___x_2983_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2__spec__2_spec__4___closed__12);
                                v_extraMsg_2944_ = v___x_2983_;
                                v___y_2945_ = v_a_2931_;
                                v___y_2946_ = v_a_2932_;
                                v___y_2947_ = v_a_2933_;
                                v___y_2948_ = v_a_2934_;
                                state = 2;
                                continue;
                            } else {
                                v_val_2984_ = leanh::lean_ctor_get(v_newName_x3f_2982_, 0);
                                leanh::lean_inc_n(v_val_2984_, 2);
                                leanh::lean_dec_ref_known(v_newName_x3f_2982_, 1);
                                v___x_2985_ = lean_st_ref_get(v_a_2934_);
                                v_env_2986_ = leanh::lean_ctor_get(v___x_2985_, 0);
                                leanh::lean_inc_ref_n(v_env_2986_, 2);
                                leanh::lean_dec(v___x_2985_);
                                v___x_2987_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Linter_checkDeprecated___closed__9
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Linter_checkDeprecated___closed__9_once
                                    ),
                                    _init_l_Lean_Linter_checkDeprecated___closed__9,
                                );
                                v___x_2988_ =
                                    l_Lean_MessageData_ofConstName(v_val_2984_, v___x_2942_);
                                leanh::lean_inc_ref(v___x_2988_);
                                v___x_2989_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2989_, 0, v___x_2987_);
                                leanh::lean_ctor_set(v___x_2989_, 1, v___x_2988_);
                                v___x_2990_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Linter_checkDeprecated___closed__11
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Linter_checkDeprecated___closed__11_once
                                    ),
                                    _init_l_Lean_Linter_checkDeprecated___closed__11,
                                );
                                v___x_2991_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2991_, 0, v___x_2989_);
                                leanh::lean_ctor_set(v___x_2991_, 1, v___x_2990_);
                                v___x_2992_ = l_Lean_Name_getPrefix(v_declName_2930_);
                                v___x_2993_ = 0;
                                leanh::lean_inc(v_declName_2930_);
                                v___x_2994_ = l_Lean_Environment_find_x3f(
                                    v_env_2986_,
                                    v_declName_2930_,
                                    v___x_2993_,
                                );
                                if leanh::lean_obj_tag(v___x_2994_) == 1 {
                                    v_val_2995_ = leanh::lean_ctor_get(v___x_2994_, 0);
                                    leanh::lean_inc(v_val_2995_);
                                    leanh::lean_dec_ref_known(v___x_2994_, 1);
                                    v___x_2996_ = l_Lean_Name_getPrefix(v_val_2984_);
                                    leanh::lean_inc(v_val_2984_);
                                    leanh::lean_inc_ref(v_env_2986_);
                                    v___x_3050_ = l_Lean_Environment_find_x3f(
                                        v_env_2986_,
                                        v_val_2984_,
                                        v___x_2993_,
                                    );
                                    if leanh::lean_obj_tag(v___x_3050_) == 1 {
                                        v_val_3051_ = leanh::lean_ctor_get(v___x_3050_, 0);
                                        leanh::lean_inc(v_val_3051_);
                                        leanh::lean_dec_ref_known(v___x_3050_, 1);
                                        v___x_3052_ = l_Lean_Meta_Context_config(v_a_2931_);
                                        v_foApprox_3053_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            0 as u32,
                                        );
                                        v_ctxApprox_3054_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            1 as u32,
                                        );
                                        v_quasiPatternApprox_3055_ =
                                            leanh::lean_ctor_get_uint8(
                                                v___x_3052_,
                                                2 as u32,
                                            );
                                        v_constApprox_3056_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            3 as u32,
                                        );
                                        v_isDefEqStuckEx_3057_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            4 as u32,
                                        );
                                        v_unificationHints_3058_ =
                                            leanh::lean_ctor_get_uint8(
                                                v___x_3052_,
                                                5 as u32,
                                            );
                                        v_proofIrrelevance_3059_ =
                                            leanh::lean_ctor_get_uint8(
                                                v___x_3052_,
                                                6 as u32,
                                            );
                                        v_assignSyntheticOpaque_3060_ =
                                            leanh::lean_ctor_get_uint8(
                                                v___x_3052_,
                                                7 as u32,
                                            );
                                        v_offsetCnstrs_3061_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            8 as u32,
                                        );
                                        v_etaStruct_3062_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            10 as u32,
                                        );
                                        v_univApprox_3063_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            11 as u32,
                                        );
                                        v_iota_3064_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            12 as u32,
                                        );
                                        v_beta_3065_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            13 as u32,
                                        );
                                        v_proj_3066_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            14 as u32,
                                        );
                                        v_zeta_3067_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            15 as u32,
                                        );
                                        v_zetaDelta_3068_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            16 as u32,
                                        );
                                        v_zetaUnused_3069_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            17 as u32,
                                        );
                                        v_zetaHave_3070_ = leanh::lean_ctor_get_uint8(
                                            v___x_3052_,
                                            18 as u32,
                                        );
                                        v_isSharedCheck_3126_ =
                                            (!leanh::lean_is_exclusive(v___x_3052_)) as u8;
                                        if v_isSharedCheck_3126_ == 0 {
                                            v___x_3072_ = v___x_3052_;
                                            v_isShared_3073_ = v_isSharedCheck_3126_;
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_3052_);
                                            v___x_3072_ = leanh::lean_box(0);
                                            v_isShared_3073_ = v_isSharedCheck_3126_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v___x_3050_);
                                        leanh::lean_dec(v___x_2996_);
                                        leanh::lean_dec(v_val_2995_);
                                        leanh::lean_dec(v___x_2992_);
                                        leanh::lean_dec_ref(v___x_2988_);
                                        leanh::lean_dec_ref(v_env_2986_);
                                        leanh::lean_dec(v_val_2984_);
                                        v_extraMsg_2944_ = v___x_2991_;
                                        v___y_2945_ = v_a_2931_;
                                        v___y_2946_ = v_a_2932_;
                                        v___y_2947_ = v_a_2933_;
                                        v___y_2948_ = v_a_2934_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_2994_);
                                    leanh::lean_dec(v___x_2992_);
                                    leanh::lean_dec_ref(v___x_2988_);
                                    leanh::lean_dec_ref(v_env_2986_);
                                    leanh::lean_dec(v_val_2984_);
                                    v_extraMsg_2944_ = v___x_2991_;
                                    v___y_2945_ = v_a_2931_;
                                    v___y_2946_ = v_a_2932_;
                                    v___y_2947_ = v_a_2933_;
                                    v___y_2948_ = v_a_2934_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_inc_ref(v_text_x3f_2981_);
                            leanh::lean_dec(v_val_2980_);
                            v_val_3127_ = leanh::lean_ctor_get(v_text_x3f_2981_, 0);
                            leanh::lean_inc(v_val_3127_);
                            leanh::lean_dec_ref_known(v_text_x3f_2981_, 1);
                            v___x_3128_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__36),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Linter_checkDeprecated___closed__36_once
                                ),
                                _init_l_Lean_Linter_checkDeprecated___closed__36,
                            );
                            v___x_3129_ = l_Lean_stringToMessageData(v_val_3127_);
                            v___x_3130_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3130_, 0, v___x_3128_);
                            leanh::lean_ctor_set(v___x_3130_, 1, v___x_3129_);
                            v_extraMsg_2944_ = v___x_3130_;
                            v___y_2945_ = v_a_2931_;
                            v___y_2946_ = v_a_2932_;
                            v___y_2947_ = v_a_2933_;
                            v___y_2948_ = v_a_2934_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2979_);
                        leanh::lean_dec(v_declName_2930_);
                        v___x_3131_ = leanh::lean_box(0);
                        if v_isShared_2940_ == 0 {
                            leanh::lean_ctor_set(v___x_2939_, 0, v___x_3131_);
                            v___x_3133_ = v___x_2939_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_3134_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
                            v___x_3133_ = v_reuseFailAlloc_3134_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_2949_ = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_;
                v___x_2950_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__1_once),
                    _init_l_Lean_Linter_checkDeprecated___closed__1,
                );
                v___x_2951_ = l_Lean_MessageData_ofConstName(v_declName_2930_, v___x_2942_);
                v___x_2952_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2952_, 0, v___x_2950_);
                leanh::lean_ctor_set(v___x_2952_, 1, v___x_2951_);
                v___x_2953_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__3_once),
                    _init_l_Lean_Linter_checkDeprecated___closed__3,
                );
                v___x_2954_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2954_, 0, v___x_2952_);
                leanh::lean_ctor_set(v___x_2954_, 1, v___x_2953_);
                v___x_2955_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2955_, 0, v___x_2954_);
                leanh::lean_ctor_set(v___x_2955_, 1, v_extraMsg_2944_);
                v___x_2956_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2956_, 0, v___x_2949_);
                leanh::lean_ctor_set(v___x_2956_, 1, v___x_2955_);
                v___x_2957_ = l_Lean_logWarning___at___00Lean_Linter_checkDeprecated_spec__1(
                    v___x_2956_,
                    v___y_2945_,
                    v___y_2946_,
                    v___y_2947_,
                    v___y_2948_,
                );
                return v___x_2957_;
            }
            3 => {
                v___x_2965_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__5_once),
                    _init_l_Lean_Linter_checkDeprecated___closed__5,
                );
                v___x_2966_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2966_, 0, v___x_2965_);
                leanh::lean_ctor_set(v___x_2966_, 1, v___y_2964_);
                v___x_2967_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__7_once),
                    _init_l_Lean_Linter_checkDeprecated___closed__7,
                );
                v___x_2968_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2968_, 0, v___x_2966_);
                leanh::lean_ctor_set(v___x_2968_, 1, v___x_2967_);
                v___x_2969_ = l_Lean_MessageData_note(v___x_2968_);
                v___x_2970_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2970_, 0, v___y_2960_);
                leanh::lean_ctor_set(v___x_2970_, 1, v___x_2969_);
                v_extraMsg_2944_ = v___x_2970_;
                v___y_2945_ = v___y_2962_;
                v___y_2946_ = v___y_2959_;
                v___y_2947_ = v___y_2963_;
                v___y_2948_ = v___y_2961_;
                state = 2;
                continue;
            }
            4 => {
                return v___x_2973_;
            }
            5 => {
                v___x_3004_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__1_once),
                    _init_l_Lean_Linter_checkDeprecated___closed__1,
                );
                v___x_3005_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3005_, 0, v___x_3004_);
                leanh::lean_ctor_set(v___x_3005_, 1, v___x_2988_);
                v___x_3006_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__13_once),
                    _init_l_Lean_Linter_checkDeprecated___closed__13,
                );
                v___x_3007_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3007_, 0, v___x_3005_);
                leanh::lean_ctor_set(v___x_3007_, 1, v___x_3006_);
                v___x_3008_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3008_, 0, v___x_3007_);
                leanh::lean_ctor_set(v___x_3008_, 1, v___y_3003_);
                v___x_3009_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__15_once),
                    _init_l_Lean_Linter_checkDeprecated___closed__15,
                );
                v___x_3010_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3010_, 0, v___x_3008_);
                leanh::lean_ctor_set(v___x_3010_, 1, v___x_3009_);
                v___x_3011_ = l_Lean_MessageData_ofName(v___x_2996_);
                v___x_3012_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3012_, 0, v___x_3010_);
                leanh::lean_ctor_set(v___x_3012_, 1, v___x_3011_);
                v___x_3013_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__17),
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__17_once),
                    _init_l_Lean_Linter_checkDeprecated___closed__17,
                );
                v___x_3014_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3014_, 0, v___x_3012_);
                leanh::lean_ctor_set(v___x_3014_, 1, v___x_3013_);
                v___x_3015_ = l_Lean_MessageData_note(v___x_3014_);
                v___x_3016_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3016_, 0, v___y_2999_);
                leanh::lean_ctor_set(v___x_3016_, 1, v___x_3015_);
                v_extraMsg_2944_ = v___x_3016_;
                v___y_2945_ = v___y_3001_;
                v___y_2946_ = v___y_2998_;
                v___y_2947_ = v___y_3002_;
                v___y_2948_ = v___y_3000_;
                state = 2;
                continue;
            }
            6 => {
                if v___y_3024_ == 0 {
                    leanh::lean_inc(v_declName_2930_);
                    leanh::lean_inc_ref(v_env_2986_);
                    v___x_3025_ = l_Lean_isProtected(v_env_2986_, v_declName_2930_);
                    if v___x_3025_ == 0 {
                        if v___x_2942_ == 0 {
                            leanh::lean_dec(v___x_2996_);
                            leanh::lean_dec_ref(v___x_2988_);
                            leanh::lean_dec_ref(v_env_2986_);
                            leanh::lean_dec(v_val_2984_);
                            v_extraMsg_2944_ = v___y_3020_;
                            v___y_2945_ = v___y_3022_;
                            v___y_2946_ = v___y_3018_;
                            v___y_2947_ = v___y_3023_;
                            v___y_2948_ = v___y_3021_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3026_ = l_Lean_isProtected(v_env_2986_, v_val_2984_);
                            if v___x_3026_ == 0 {
                                leanh::lean_dec(v___x_2996_);
                                leanh::lean_dec_ref(v___x_2988_);
                                v_extraMsg_2944_ = v___y_3020_;
                                v___y_2945_ = v___y_3022_;
                                v___y_2946_ = v___y_3018_;
                                v___y_2947_ = v___y_3023_;
                                v___y_2948_ = v___y_3021_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v___x_2996_);
                                v___x_3027_ = l_Lean_Name_componentsRev(v___x_2996_);
                                v___x_3028_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3029_ = l_List_lengthTR___redArg(v___x_3027_);
                                v___x_3030_ = lean_nat_dec_lt(v___x_3028_, v___x_3029_);
                                leanh::lean_dec(v___x_3029_);
                                if v___x_3030_ == 0 {
                                    leanh::lean_dec(v___x_3027_);
                                    v___x_3031_ = leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Linter_checkDeprecated___closed__19
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Linter_checkDeprecated___closed__19_once
                                        ),
                                        _init_l_Lean_Linter_checkDeprecated___closed__19,
                                    );
                                    v___y_2998_ = v___y_3018_;
                                    v___y_2999_ = v___y_3020_;
                                    v___y_3000_ = v___y_3021_;
                                    v___y_3001_ = v___y_3022_;
                                    v___y_3002_ = v___y_3023_;
                                    v___y_3003_ = v___x_3031_;
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_3032_ = leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Linter_checkDeprecated___closed__21
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Linter_checkDeprecated___closed__21_once
                                        ),
                                        _init_l_Lean_Linter_checkDeprecated___closed__21,
                                    );
                                    v___x_3033_ = leanh::lean_unsigned_to_nat(0);
                                    v___x_3034_ = l_List_get___redArg(v___x_3027_, v___x_3033_);
                                    leanh::lean_dec(v___x_3027_);
                                    v___x_3035_ = l_Lean_MessageData_ofName(v___x_3034_);
                                    v___x_3036_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3036_, 0, v___x_3032_);
                                    leanh::lean_ctor_set(v___x_3036_, 1, v___x_3035_);
                                    v___x_3037_ = leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Linter_checkDeprecated___closed__23
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Linter_checkDeprecated___closed__23_once
                                        ),
                                        _init_l_Lean_Linter_checkDeprecated___closed__23,
                                    );
                                    v___x_3038_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3038_, 0, v___x_3036_);
                                    leanh::lean_ctor_set(v___x_3038_, 1, v___x_3037_);
                                    v___y_2998_ = v___y_3018_;
                                    v___y_2999_ = v___y_3020_;
                                    v___y_3000_ = v___y_3021_;
                                    v___y_3001_ = v___y_3022_;
                                    v___y_3002_ = v___y_3023_;
                                    v___y_3003_ = v___x_3038_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2996_);
                        leanh::lean_dec_ref(v___x_2988_);
                        leanh::lean_dec_ref(v_env_2986_);
                        leanh::lean_dec(v_val_2984_);
                        v_extraMsg_2944_ = v___y_3020_;
                        v___y_2945_ = v___y_3022_;
                        v___y_2946_ = v___y_3018_;
                        v___y_2947_ = v___y_3023_;
                        v___y_2948_ = v___y_3021_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2996_);
                    leanh::lean_dec_ref(v___x_2988_);
                    leanh::lean_dec_ref(v_env_2986_);
                    if leanh::lean_obj_tag(v_declName_2930_) == 1 {
                        v_str_3039_ = leanh::lean_ctor_get(v_declName_2930_, 1);
                        v___x_3040_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_checkDeprecated___closed__25_once
                            ),
                            _init_l_Lean_Linter_checkDeprecated___closed__25,
                        );
                        leanh::lean_inc_ref(v_str_3039_);
                        v___x_3041_ = l_Lean_stringToMessageData(v_str_3039_);
                        v___x_3042_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3042_, 0, v___x_3040_);
                        leanh::lean_ctor_set(v___x_3042_, 1, v___x_3041_);
                        v___x_3043_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__27),
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_checkDeprecated___closed__27_once
                            ),
                            _init_l_Lean_Linter_checkDeprecated___closed__27,
                        );
                        v___x_3044_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3044_, 0, v___x_3042_);
                        leanh::lean_ctor_set(v___x_3044_, 1, v___x_3043_);
                        v___x_3045_ = l_Lean_MessageData_ofConstName(v_val_2984_, v___y_3019_);
                        v___x_3046_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3046_, 0, v___x_3044_);
                        leanh::lean_ctor_set(v___x_3046_, 1, v___x_3045_);
                        v___x_3047_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__29),
                            core::ptr::addr_of_mut!(
                                l_Lean_Linter_checkDeprecated___closed__29_once
                            ),
                            _init_l_Lean_Linter_checkDeprecated___closed__29,
                        );
                        v___x_3048_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3048_, 0, v___x_3046_);
                        leanh::lean_ctor_set(v___x_3048_, 1, v___x_3047_);
                        v___y_2959_ = v___y_3018_;
                        v___y_2960_ = v___y_3020_;
                        v___y_2961_ = v___y_3021_;
                        v___y_2962_ = v___y_3022_;
                        v___y_2963_ = v___y_3023_;
                        v___y_2964_ = v___x_3048_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_2984_);
                        v___x_3049_ = l_Lean_MessageData_nil;
                        v___y_2959_ = v___y_3018_;
                        v___y_2960_ = v___y_3020_;
                        v___y_2961_ = v___y_3021_;
                        v___y_2962_ = v___y_3022_;
                        v___y_2963_ = v___y_3023_;
                        v___y_2964_ = v___x_3049_;
                        state = 3;
                        continue;
                    }
                }
            }
            7 => {
                v_trackZetaDelta_3074_ = leanh::lean_ctor_get_uint8(
                    v_a_2931_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3075_ = leanh::lean_ctor_get(v_a_2931_, 1);
                v_lctx_3076_ = leanh::lean_ctor_get(v_a_2931_, 2);
                v_localInstances_3077_ = leanh::lean_ctor_get(v_a_2931_, 3);
                v_defEqCtx_x3f_3078_ = leanh::lean_ctor_get(v_a_2931_, 4);
                v_synthPendingDepth_3079_ = leanh::lean_ctor_get(v_a_2931_, 5);
                v_canUnfold_x3f_3080_ = leanh::lean_ctor_get(v_a_2931_, 6);
                v_univApprox_3081_ = leanh::lean_ctor_get_uint8(
                    v_a_2931_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3082_ = leanh::lean_ctor_get_uint8(
                    v_a_2931_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3083_ = leanh::lean_ctor_get_uint8(
                    v_a_2931_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3084_ = 2;
                if v_isShared_3073_ == 0 {
                    v_config_3086_ = v___x_3072_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        0 as u32,
                        v_foApprox_3053_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        1 as u32,
                        v_ctxApprox_3054_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        2 as u32,
                        v_quasiPatternApprox_3055_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        3 as u32,
                        v_constApprox_3056_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        4 as u32,
                        v_isDefEqStuckEx_3057_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        5 as u32,
                        v_unificationHints_3058_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        6 as u32,
                        v_proofIrrelevance_3059_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        7 as u32,
                        v_assignSyntheticOpaque_3060_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        8 as u32,
                        v_offsetCnstrs_3061_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        10 as u32,
                        v_etaStruct_3062_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        11 as u32,
                        v_univApprox_3063_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        12 as u32,
                        v_iota_3064_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        13 as u32,
                        v_beta_3065_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        14 as u32,
                        v_proj_3066_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        15 as u32,
                        v_zeta_3067_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        16 as u32,
                        v_zetaDelta_3068_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        17 as u32,
                        v_zetaUnused_3069_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        18 as u32,
                        v_zetaHave_3070_,
                    );
                    v_config_3086_ = v_reuseFailAlloc_3125_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_ctor_set_uint8(v_config_3086_, 9 as u32, v___x_3084_);
                v___x_3087_ = l_Lean_Meta_Context_configKey(v_a_2931_);
                v___x_3088_ = 3u64;
                v___x_3089_ = lean_uint64_shift_right(v___x_3087_, v___x_3088_);
                v___x_3090_ = l_Lean_ConstantInfo_type(v_val_2995_);
                leanh::lean_dec(v_val_2995_);
                v___x_3091_ = l_Lean_ConstantInfo_type(v_val_3051_);
                leanh::lean_dec(v_val_3051_);
                v___x_3092_ = lean_uint64_shift_left(v___x_3089_, v___x_3088_);
                v___x_3093_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__30),
                    core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__30_once),
                    _init_l_Lean_Linter_checkDeprecated___closed__30,
                );
                v_key_3094_ = lean_uint64_lor(v___x_3092_, v___x_3093_);
                v___x_3095_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_3095_, 0, v_config_3086_);
                leanh::lean_ctor_set_uint64(
                    v___x_3095_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_3094_,
                );
                leanh::lean_inc(v_canUnfold_x3f_3080_);
                leanh::lean_inc(v_synthPendingDepth_3079_);
                leanh::lean_inc(v_defEqCtx_x3f_3078_);
                leanh::lean_inc_ref(v_localInstances_3077_);
                leanh::lean_inc_ref(v_lctx_3076_);
                leanh::lean_inc(v_zetaDeltaSet_3075_);
                v___x_3096_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_3096_, 0, v___x_3095_);
                leanh::lean_ctor_set(v___x_3096_, 1, v_zetaDeltaSet_3075_);
                leanh::lean_ctor_set(v___x_3096_, 2, v_lctx_3076_);
                leanh::lean_ctor_set(v___x_3096_, 3, v_localInstances_3077_);
                leanh::lean_ctor_set(v___x_3096_, 4, v_defEqCtx_x3f_3078_);
                leanh::lean_ctor_set(v___x_3096_, 5, v_synthPendingDepth_3079_);
                leanh::lean_ctor_set(v___x_3096_, 6, v_canUnfold_x3f_3080_);
                leanh::lean_ctor_set_uint8(
                    v___x_3096_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3074_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3096_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3081_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3096_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3082_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3096_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3083_,
                );
                leanh::lean_inc_ref(v___x_3091_);
                leanh::lean_inc_ref(v___x_3090_);
                v___x_3097_ = l_Lean_Meta_isExprDefEqGuarded(
                    v___x_3090_,
                    v___x_3091_,
                    v___x_3096_,
                    v_a_2932_,
                    v_a_2933_,
                    v_a_2934_,
                );
                leanh::lean_dec_ref_known(v___x_3096_, 7);
                if leanh::lean_obj_tag(v___x_3097_) == 0 {
                    v_a_3098_ = leanh::lean_ctor_get(v___x_3097_, 0);
                    leanh::lean_inc(v_a_3098_);
                    leanh::lean_dec_ref_known(v___x_3097_, 1);
                    v___x_3107_ = (leanh::lean_unbox(v_a_3098_) as u8);
                    leanh::lean_dec(v_a_3098_);
                    if v___x_3107_ == 0 {
                        if v___x_2942_ == 0 {
                            leanh::lean_dec_ref(v___x_3091_);
                            leanh::lean_dec_ref(v___x_3090_);
                            v_msg_3100_ = v___x_2991_;
                            v___y_3101_ = v_a_2931_;
                            v___y_3102_ = v_a_2932_;
                            v___y_3103_ = v_a_2933_;
                            v___y_3104_ = v_a_2934_;
                            state = 9;
                            continue;
                        } else {
                            v___x_3108_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__32),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Linter_checkDeprecated___closed__32_once
                                ),
                                _init_l_Lean_Linter_checkDeprecated___closed__32,
                            );
                            v___x_3109_ = l_Lean_indentExpr(v___x_3091_);
                            v___x_3110_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3110_, 0, v___x_3108_);
                            leanh::lean_ctor_set(v___x_3110_, 1, v___x_3109_);
                            v___x_3111_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Linter_checkDeprecated___closed__34),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Linter_checkDeprecated___closed__34_once
                                ),
                                _init_l_Lean_Linter_checkDeprecated___closed__34,
                            );
                            v___x_3112_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3112_, 0, v___x_3110_);
                            leanh::lean_ctor_set(v___x_3112_, 1, v___x_3111_);
                            v___x_3113_ = l_Lean_indentExpr(v___x_3090_);
                            v___x_3114_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3114_, 0, v___x_3112_);
                            leanh::lean_ctor_set(v___x_3114_, 1, v___x_3113_);
                            v___x_3115_ = l_Lean_MessageData_note(v___x_3114_);
                            v___x_3116_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3116_, 0, v___x_2991_);
                            leanh::lean_ctor_set(v___x_3116_, 1, v___x_3115_);
                            v_msg_3100_ = v___x_3116_;
                            v___y_3101_ = v_a_2931_;
                            v___y_3102_ = v_a_2932_;
                            v___y_3103_ = v_a_2933_;
                            v___y_3104_ = v_a_2934_;
                            state = 9;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3091_);
                        leanh::lean_dec_ref(v___x_3090_);
                        v_msg_3100_ = v___x_2991_;
                        v___y_3101_ = v_a_2931_;
                        v___y_3102_ = v_a_2932_;
                        v___y_3103_ = v_a_2933_;
                        v___y_3104_ = v_a_2934_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3091_);
                    leanh::lean_dec_ref(v___x_3090_);
                    leanh::lean_dec(v___x_2996_);
                    leanh::lean_dec(v___x_2992_);
                    leanh::lean_dec_ref_known(v___x_2991_, 2);
                    leanh::lean_dec_ref(v___x_2988_);
                    leanh::lean_dec_ref(v_env_2986_);
                    leanh::lean_dec(v_val_2984_);
                    leanh::lean_dec(v_declName_2930_);
                    v_a_3117_ = leanh::lean_ctor_get(v___x_3097_, 0);
                    v_isSharedCheck_3124_ = (!leanh::lean_is_exclusive(v___x_3097_)) as u8;
                    if v_isSharedCheck_3124_ == 0 {
                        v___x_3119_ = v___x_3097_;
                        v_isShared_3120_ = v_isSharedCheck_3124_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3117_);
                        leanh::lean_dec(v___x_3097_);
                        v___x_3119_ = leanh::lean_box(0);
                        v_isShared_3120_ = v_isSharedCheck_3124_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3105_ = l_Lean_Name_isAnonymous(v___x_2992_);
                if v___x_3105_ == 0 {
                    v___x_3106_ = lean_name_eq(v___x_2992_, v___x_2996_);
                    leanh::lean_dec(v___x_2992_);
                    if v___x_3106_ == 0 {
                        v___y_3018_ = v___y_3102_;
                        v___y_3019_ = v___x_3105_;
                        v___y_3020_ = v_msg_3100_;
                        v___y_3021_ = v___y_3104_;
                        v___y_3022_ = v___y_3101_;
                        v___y_3023_ = v___y_3103_;
                        v___y_3024_ = v___x_2942_;
                        state = 6;
                        continue;
                    } else {
                        v___y_3018_ = v___y_3102_;
                        v___y_3019_ = v___x_3105_;
                        v___y_3020_ = v_msg_3100_;
                        v___y_3021_ = v___y_3104_;
                        v___y_3022_ = v___y_3101_;
                        v___y_3023_ = v___y_3103_;
                        v___y_3024_ = v___x_3105_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2996_);
                    leanh::lean_dec(v___x_2992_);
                    leanh::lean_dec_ref(v___x_2988_);
                    leanh::lean_dec_ref(v_env_2986_);
                    leanh::lean_dec(v_val_2984_);
                    v_extraMsg_2944_ = v_msg_3100_;
                    v___y_2945_ = v___y_3101_;
                    v___y_2946_ = v___y_3102_;
                    v___y_2947_ = v___y_3103_;
                    v___y_2948_ = v___y_3104_;
                    state = 2;
                    continue;
                }
            }
            10 => {
                if v_isShared_3120_ == 0 {
                    v___x_3122_ = v___x_3119_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3122_;
            }
            12 => {
                return v___x_3133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_checkDeprecated___boxed(
    mut v_declName_3136_: *mut leanh::LeanObject,
    mut v_a_3137_: *mut leanh::LeanObject,
    mut v_a_3138_: *mut leanh::LeanObject,
    mut v_a_3139_: *mut leanh::LeanObject,
    mut v_a_3140_: *mut leanh::LeanObject,
    mut v_a_3141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3142_ =
        l_Lean_Linter_checkDeprecated(v_declName_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_);
    leanh::lean_dec(v_a_3140_);
    leanh::lean_dec_ref(v_a_3139_);
    leanh::lean_dec(v_a_3138_);
    leanh::lean_dec_ref(v_a_3137_);
    return v_res_3142_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(
    mut v_o_3143_: *mut leanh::LeanObject,
    mut v___y_3144_: *mut leanh::LeanObject,
    mut v___y_3145_: *mut leanh::LeanObject,
    mut v___y_3146_: *mut leanh::LeanObject,
    mut v___y_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3149_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___redArg(v_o_3143_, v___y_3147_);
    return v___x_3149_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0___boxed(
    mut v_o_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
    mut v___y_3153_: *mut leanh::LeanObject,
    mut v___y_3154_: *mut leanh::LeanObject,
    mut v___y_3155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3156_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_checkDeprecated_spec__0_spec__0(v_o_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
    leanh::lean_dec(v___y_3154_);
    leanh::lean_dec_ref(v___y_3153_);
    leanh::lean_dec(v___y_3152_);
    leanh::lean_dec_ref(v___y_3151_);
    return v_res_3156_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Deprecated(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1975727962____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_deprecated = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Linter_linter_deprecated);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_Deprecated_0__Lean_Linter_initFn_00___x40_Lean_Linter_Deprecated_1482207894____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_deprecatedAttr = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Linter_deprecatedAttr);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Deprecated(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Deprecated(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Init(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_InfoTree_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Deprecated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Deprecated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_Deprecated(builtin);
}
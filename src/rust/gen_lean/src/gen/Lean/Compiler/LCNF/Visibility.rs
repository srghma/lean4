// Lean compiler output
// Module: Lean.Compiler.LCNF.Visibility
// Imports: Lean.Compiler.ImplementedByAttr Lean.ExtraModUses Lean.Compiler.Options Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.PassManager
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_size, lean_array_uget_borrowed, lean_name_eq, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Compiler::ImplementedByAttr::{
    initialize_Lean_Compiler_ImplementedByAttr, runtime_initialize_Lean_Compiler_ImplementedByAttr,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_Code_sizeLe, l_Lean_Compiler_LCNF_Decl_castPurity_x21,
    l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_Phase_toPurity, l_Lean_Compiler_LCNF_getPhase___redArg,
    l_Lean_Compiler_LCNF_getPurity___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::ConfigOptions::l_Lean_Compiler_LCNF_compiler_small;
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, l_Lean_Compiler_LCNF_baseExt,
    l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg, l_Lean_Compiler_LCNF_isDeclTransparent,
    l_Lean_Compiler_LCNF_setDeclTransparent, runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::Compiler::LCNF::PublicDeclsExt::{
    l_Lean_Compiler_LCNF_isDeclPublic, l_Lean_Compiler_LCNF_setDeclPublic,
};
use crate::r#gen::Lean::Compiler::MetaAttr::{l_Lean_getIRPhases, l_Lean_isMarkedMeta};
use crate::r#gen::Lean::Compiler::Options::{
    initialize_Lean_Compiler_Options, l_Lean_Compiler_compiler_checkMeta,
    l_Lean_Compiler_compiler_inLeanIR, l_Lean_Compiler_compiler_relaxedMetaCheck,
    runtime_initialize_Lean_Compiler_Options,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_instInhabited,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_isImportedConst, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg, l_Lean_instBEqConstantKind_beq,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::ExtraModUses::{
    initialize_Lean_ExtraModUses, l___private_Lean_ExtraModUses_0__Lean_extraModUses,
    l_Lean_indirectModUseExt, l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
    runtime_initialize_Lean_ExtraModUses,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Setup::l_Lean_instBEqIRPhases_beq;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [105, 110, 102, 101, 114, 86, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,12284906337363465325 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [77, 97, 114, 107, 105, 110, 103, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_value:
    crate::leanh::LeanStringObject<65> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 65,
    m_capacity: 65,
    m_length: 64,
    m_data: [
        32, 97, 115, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 116, 32, 98, 101, 99, 97,
        117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 111, 112, 97, 113, 117, 101, 32, 97, 110,
        100, 32, 105, 116, 115, 32, 98, 111, 100, 121, 32, 108, 111, 111, 107, 115, 32, 114, 101,
        108, 101, 118, 97, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [32, 97, 115, 32, 111, 112, 97, 113, 117, 101, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 117, 115, 101, 100, 32, 98, 121, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 116, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [96, 44, 32, 109, 97, 121, 32, 110, 111, 116, 32, 97, 99, 99, 101, 115, 115, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [96, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 96, 109, 101, 116, 97, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6_value: crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [96, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 97, 115, 32, 96, 109, 101, 116, 97, 96, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 109, 101, 116, 97, 96, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [96, 44, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14_value: crate::leanh::LeanStringObject<63> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 32, 104, 101, 114, 101, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 109, 101, 116, 97, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 110, 111, 116, 32, 109, 97, 114, 107, 101, 100, 32, 96, 109, 101, 116, 97, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 112, 117, 98, 108, 105, 99, 32, 96, 109, 101, 116, 97, 96, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20_value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 32, 104, 101, 114, 101, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1_value: crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [67, 97, 110, 110, 111, 116, 32, 99, 111, 109, 112, 105, 108, 101, 32, 105, 110, 108, 105, 110, 101, 47, 115, 112, 101, 99, 105, 97, 108, 105, 122, 105, 110, 103, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [96, 32, 97, 115, 32, 105, 116, 32, 117, 115, 101, 115, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [96, 32, 111, 102, 32, 109, 111, 100, 117, 108, 101, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7_value: crate::leanh::LeanStringObject<80> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 80, m_capacity: 80, m_length: 79, m_data: [96, 32, 119, 104, 105, 99, 104, 32, 109, 117, 115, 116, 32, 98, 101, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 117, 98, 108, 105, 99, 108, 121, 46, 32, 84, 104, 105, 115, 32, 108, 105, 109, 105, 116, 97, 116, 105, 111, 110, 32, 109, 97, 121, 32, 98, 101, 32, 108, 105, 102, 116, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 102, 117, 116, 117, 114, 101, 46, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        99, 104, 101, 99, 107, 84, 101, 109, 112, 108, 97, 116, 101, 86, 105, 115, 105, 98, 105,
        108, 105, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15185984258296179725 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_checkTemplateVisibility: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [32, 97, 115, 32, 111, 112, 97, 113, 117, 101, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 97, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 102, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_inferVisibility___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,3059348757014389675 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_inferVisibility___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_inferVisibility___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [86, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7864849472683266603 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,270195162246034326 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11649833169365808703 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,10150642787462906833 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15828838177423456980 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14679371497876971281 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9775471812865212668 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15772378170105911453 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,9088531055874635291 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4427328837111778918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15667018320580198296 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(
    mut v_e_2648_: *mut crate::leanh::LeanObject,
    mut v_s_2649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_e_2648_) {
        3 => {
            let mut v_declName_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_declName_2650_ = crate::leanh::lean_ctor_get(v_e_2648_, 0);
            crate::leanh::lean_inc(v_declName_2650_);
            crate::leanh::lean_dec_ref_known(v_e_2648_, 3);
            v___x_2651_ = l_Lean_NameSet_insert(v_s_2649_, v_declName_2650_);
            return v___x_2651_;
        }
        9 => {
            let mut v_fn_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fn_2652_ = crate::leanh::lean_ctor_get(v_e_2648_, 0);
            crate::leanh::lean_inc(v_fn_2652_);
            crate::leanh::lean_dec_ref_known(v_e_2648_, 2);
            v___x_2653_ = l_Lean_NameSet_insert(v_s_2649_, v_fn_2652_);
            return v___x_2653_;
        }
        10 => {
            let mut v_fn_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fn_2654_ = crate::leanh::lean_ctor_get(v_e_2648_, 0);
            crate::leanh::lean_inc(v_fn_2654_);
            crate::leanh::lean_dec_ref_known(v_e_2648_, 2);
            v___x_2655_ = l_Lean_NameSet_insert(v_s_2649_, v_fn_2654_);
            return v___x_2655_;
        }
        _ => {
            crate::leanh::lean_dec(v_e_2648_);
            return v_s_2649_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue(
    mut v_pu_2656_: u8,
    mut v_e_2657_: *mut crate::leanh::LeanObject,
    mut v_s_2658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2659_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(v_e_2657_, v_s_2658_);
    return v___x_2659_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___boxed(
    mut v_pu_2660_: *mut crate::leanh::LeanObject,
    mut v_e_2661_: *mut crate::leanh::LeanObject,
    mut v_s_2662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2663_: u8 = 0;
    let mut v_res_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2663_ = (crate::leanh::lean_unbox(v_pu_2660_) as u8);
    v_res_2664_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue(v_pu_boxed_2663_, v_e_2661_, v_s_2662_);
    return v_res_2664_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(
    mut v_pu_2665_: u8,
    mut v_code_2666_: *mut crate::leanh::LeanObject,
    mut v_s_2667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: usize = 0;
    let mut v___x_2690_: usize = 0;
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: usize = 0;
    let mut v___x_2693_: usize = 0;
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_2666_) {
                0 => {
                    v_decl_2668_ = crate::leanh::lean_ctor_get(v_code_2666_, 0);
                    crate::leanh::lean_inc_ref(v_decl_2668_);
                    v_k_2669_ = crate::leanh::lean_ctor_get(v_code_2666_, 1);
                    crate::leanh::lean_inc_ref(v_k_2669_);
                    crate::leanh::lean_dec_ref_known(v_code_2666_, 2);
                    v_value_2670_ = crate::leanh::lean_ctor_get(v_decl_2668_, 3);
                    crate::leanh::lean_inc(v_value_2670_);
                    crate::leanh::lean_dec_ref(v_decl_2668_);
                    v___x_2671_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(v_value_2670_, v_s_2667_);
                    v_code_2666_ = v_k_2669_;
                    v_s_2667_ = v___x_2671_;
                    state = 0;
                    continue;
                }
                2 => {
                    v_decl_2673_ = crate::leanh::lean_ctor_get(v_code_2666_, 0);
                    crate::leanh::lean_inc_ref(v_decl_2673_);
                    v_k_2674_ = crate::leanh::lean_ctor_get(v_code_2666_, 1);
                    crate::leanh::lean_inc_ref(v_k_2674_);
                    crate::leanh::lean_dec_ref_known(v_code_2666_, 2);
                    v_value_2675_ = crate::leanh::lean_ctor_get(v_decl_2673_, 4);
                    crate::leanh::lean_inc_ref(v_value_2675_);
                    crate::leanh::lean_dec_ref(v_decl_2673_);
                    v___x_2676_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_2665_, v_k_2674_, v_s_2667_);
                    v_code_2666_ = v_value_2675_;
                    v_s_2667_ = v___x_2676_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_2678_ = crate::leanh::lean_ctor_get(v_code_2666_, 0);
                    crate::leanh::lean_inc_ref(v_decl_2678_);
                    v_k_2679_ = crate::leanh::lean_ctor_get(v_code_2666_, 1);
                    crate::leanh::lean_inc_ref(v_k_2679_);
                    crate::leanh::lean_dec_ref_known(v_code_2666_, 2);
                    v_value_2680_ = crate::leanh::lean_ctor_get(v_decl_2678_, 4);
                    crate::leanh::lean_inc_ref(v_value_2680_);
                    crate::leanh::lean_dec_ref(v_decl_2678_);
                    v___x_2681_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_2665_, v_k_2679_, v_s_2667_);
                    v_code_2666_ = v_value_2680_;
                    v_s_2667_ = v___x_2681_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_cases_2683_ = crate::leanh::lean_ctor_get(v_code_2666_, 0);
                    crate::leanh::lean_inc_ref(v_cases_2683_);
                    crate::leanh::lean_dec_ref_known(v_code_2666_, 1);
                    v_alts_2684_ = crate::leanh::lean_ctor_get(v_cases_2683_, 3);
                    crate::leanh::lean_inc_ref(v_alts_2684_);
                    crate::leanh::lean_dec_ref(v_cases_2683_);
                    v___x_2685_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2686_ = lean_array_get_size(v_alts_2684_);
                    v___x_2687_ = lean_nat_dec_lt(v___x_2685_, v___x_2686_);
                    if v___x_2687_ == 0 {
                        crate::leanh::lean_dec_ref(v_alts_2684_);
                        return v_s_2667_;
                    } else {
                        v___x_2688_ = lean_nat_dec_le(v___x_2686_, v___x_2686_);
                        if v___x_2688_ == 0 {
                            if v___x_2687_ == 0 {
                                crate::leanh::lean_dec_ref(v_alts_2684_);
                                return v_s_2667_;
                            } else {
                                v___x_2689_ = 0usize;
                                v___x_2690_ = lean_usize_of_nat(v___x_2686_);
                                v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_2665_, v_alts_2684_, v___x_2689_, v___x_2690_, v_s_2667_);
                                crate::leanh::lean_dec_ref(v_alts_2684_);
                                return v___x_2691_;
                            }
                        } else {
                            v___x_2692_ = 0usize;
                            v___x_2693_ = lean_usize_of_nat(v___x_2686_);
                            v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_2665_, v_alts_2684_, v___x_2692_, v___x_2693_, v_s_2667_);
                            crate::leanh::lean_dec_ref(v_alts_2684_);
                            return v___x_2694_;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_code_2666_);
                    return v_s_2667_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(
    mut v_pu_2695_: u8,
    mut v_as_2696_: *mut crate::leanh::LeanObject,
    mut v_i_2697_: usize,
    mut v_stop_2698_: usize,
    mut v_b_2699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: usize = 0;
    let mut v___x_2703_: usize = 0;
    let mut v___x_2705_: u8 = 0;
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2705_ = lean_usize_dec_eq(v_i_2697_, v_stop_2698_);
                if v___x_2705_ == 0 {
                    v___x_2706_ = lean_array_uget_borrowed(v_as_2696_, v_i_2697_);
                    match crate::leanh::lean_obj_tag(v___x_2706_) {
                        0 => {
                            v_code_2707_ = crate::leanh::lean_ctor_get(v___x_2706_, 2);
                            crate::leanh::lean_inc_ref(v_code_2707_);
                            v___x_2708_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_2695_, v_code_2707_, v_b_2699_);
                            v___y_2701_ = v___x_2708_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_2709_ = crate::leanh::lean_ctor_get(v___x_2706_, 1);
                            crate::leanh::lean_inc_ref(v_code_2709_);
                            v___x_2710_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_2695_, v_code_2709_, v_b_2699_);
                            v___y_2701_ = v___x_2710_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_2711_ = crate::leanh::lean_ctor_get(v___x_2706_, 0);
                            crate::leanh::lean_inc_ref(v_code_2711_);
                            v___x_2712_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_2695_, v_code_2711_, v_b_2699_);
                            v___y_2701_ = v___x_2712_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_2699_;
                }
            }
            1 => {
                v___x_2702_ = 1usize;
                v___x_2703_ = lean_usize_add(v_i_2697_, v___x_2702_);
                v_i_2697_ = v___x_2703_;
                v_b_2699_ = v___y_2701_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0___boxed(
    mut v_pu_2713_: *mut crate::leanh::LeanObject,
    mut v_as_2714_: *mut crate::leanh::LeanObject,
    mut v_i_2715_: *mut crate::leanh::LeanObject,
    mut v_stop_2716_: *mut crate::leanh::LeanObject,
    mut v_b_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2718_: u8 = 0;
    let mut v_i_boxed_2719_: usize = 0;
    let mut v_stop_boxed_2720_: usize = 0;
    let mut v_res_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2718_ = (crate::leanh::lean_unbox(v_pu_2713_) as u8);
    v_i_boxed_2719_ = crate::leanh::lean_unbox_usize(v_i_2715_);
    crate::leanh::lean_dec(v_i_2715_);
    v_stop_boxed_2720_ = crate::leanh::lean_unbox_usize(v_stop_2716_);
    crate::leanh::lean_dec(v_stop_2716_);
    v_res_2721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_boxed_2718_, v_as_2714_, v_i_boxed_2719_, v_stop_boxed_2720_, v_b_2717_);
    crate::leanh::lean_dec_ref(v_as_2714_);
    return v_res_2721_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls___boxed(
    mut v_pu_2722_: *mut crate::leanh::LeanObject,
    mut v_code_2723_: *mut crate::leanh::LeanObject,
    mut v_s_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2725_: u8 = 0;
    let mut v_res_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2725_ = (crate::leanh::lean_unbox(v_pu_2722_) as u8);
    v_res_2726_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(
        v_pu_boxed_2725_,
        v_code_2723_,
        v_s_2724_,
    );
    return v_res_2726_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(
    mut v_opts_2727_: *mut crate::leanh::LeanObject,
    mut v_opt_2728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2729_ = crate::leanh::lean_ctor_get(v_opt_2728_, 0);
    v_defValue_2730_ = crate::leanh::lean_ctor_get(v_opt_2728_, 1);
    v_map_2731_ = crate::leanh::lean_ctor_get(v_opts_2727_, 0);
    v___x_2732_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2731_,
            v_name_2729_,
        );
    if crate::leanh::lean_obj_tag(v___x_2732_) == 0 {
        crate::leanh::lean_inc(v_defValue_2730_);
        return v_defValue_2730_;
    } else {
        let mut v_val_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2733_ = crate::leanh::lean_ctor_get(v___x_2732_, 0);
        crate::leanh::lean_inc(v_val_2733_);
        crate::leanh::lean_dec_ref_known(v___x_2732_, 1);
        if crate::leanh::lean_obj_tag(v_val_2733_) == 3 {
            let mut v_v_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_2734_ = crate::leanh::lean_ctor_get(v_val_2733_, 0);
            crate::leanh::lean_inc(v_v_2734_);
            crate::leanh::lean_dec_ref_known(v_val_2733_, 1);
            return v_v_2734_;
        } else {
            crate::leanh::lean_dec(v_val_2733_);
            crate::leanh::lean_inc(v_defValue_2730_);
            return v_defValue_2730_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0___boxed(
    mut v_opts_2735_: *mut crate::leanh::LeanObject,
    mut v_opt_2736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2737_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v_opts_2735_, v_opt_2736_);
    crate::leanh::lean_dec_ref(v_opt_2736_);
    crate::leanh::lean_dec_ref(v_opts_2735_);
    return v_res_2737_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(
    mut v_v_2738_: *mut crate::leanh::LeanObject,
    mut v_f_2739_: *mut crate::leanh::LeanObject,
    mut v___y_2740_: *mut crate::leanh::LeanObject,
    mut v___y_2741_: *mut crate::leanh::LeanObject,
    mut v___y_2742_: *mut crate::leanh::LeanObject,
    mut v___y_2743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2749_: u8 = 0;
    let mut v___x_2750_: u8 = 0;
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2755_: u8 = 0;
    let mut v_unused_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_2738_) == 0 {
                    v_code_2745_ = crate::leanh::lean_ctor_get(v_v_2738_, 0);
                    crate::leanh::lean_inc_ref(v_code_2745_);
                    crate::leanh::lean_dec_ref_known(v_v_2738_, 1);
                    crate::leanh::lean_inc(v___y_2743_);
                    crate::leanh::lean_inc_ref(v___y_2742_);
                    crate::leanh::lean_inc(v___y_2741_);
                    crate::leanh::lean_inc_ref(v___y_2740_);
                    v___x_2746_ = crate::leanh::lean_apply_6(
                        v_f_2739_,
                        v_code_2745_,
                        v___y_2740_,
                        v___y_2741_,
                        v___y_2742_,
                        v___y_2743_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2746_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_2739_);
                    v_isSharedCheck_2755_ = (!crate::leanh::lean_is_exclusive(v_v_2738_)) as u8;
                    if v_isSharedCheck_2755_ == 0 {
                        v_unused_2756_ = crate::leanh::lean_ctor_get(v_v_2738_, 0);
                        crate::leanh::lean_dec(v_unused_2756_);
                        v___x_2748_ = v_v_2738_;
                        v_isShared_2749_ = v_isSharedCheck_2755_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_2738_);
                        v___x_2748_ = crate::leanh::lean_box(0);
                        v_isShared_2749_ = v_isSharedCheck_2755_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2750_ = 0;
                v___x_2751_ = crate::leanh::lean_box((v___x_2750_) as usize);
                if v_isShared_2749_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2748_, 0);
                    crate::leanh::lean_ctor_set(v___x_2748_, 0, v___x_2751_);
                    v___x_2753_ = v___x_2748_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2754_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
                    v___x_2753_ = v_reuseFailAlloc_2754_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2753_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg___boxed(
    mut v_v_2757_: *mut crate::leanh::LeanObject,
    mut v_f_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
    mut v___y_2761_: *mut crate::leanh::LeanObject,
    mut v___y_2762_: *mut crate::leanh::LeanObject,
    mut v___y_2763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2764_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_2757_, v_f_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
    crate::leanh::lean_dec(v___y_2762_);
    crate::leanh::lean_dec_ref(v___y_2761_);
    crate::leanh::lean_dec(v___y_2760_);
    crate::leanh::lean_dec_ref(v___y_2759_);
    return v_res_2764_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(
    mut v_pu_2765_: u8,
    mut v_v_2766_: *mut crate::leanh::LeanObject,
    mut v_f_2767_: *mut crate::leanh::LeanObject,
    mut v___y_2768_: *mut crate::leanh::LeanObject,
    mut v___y_2769_: *mut crate::leanh::LeanObject,
    mut v___y_2770_: *mut crate::leanh::LeanObject,
    mut v___y_2771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2773_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_2766_, v_f_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
    return v___x_2773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___boxed(
    mut v_pu_2774_: *mut crate::leanh::LeanObject,
    mut v_v_2775_: *mut crate::leanh::LeanObject,
    mut v_f_2776_: *mut crate::leanh::LeanObject,
    mut v___y_2777_: *mut crate::leanh::LeanObject,
    mut v___y_2778_: *mut crate::leanh::LeanObject,
    mut v___y_2779_: *mut crate::leanh::LeanObject,
    mut v___y_2780_: *mut crate::leanh::LeanObject,
    mut v___y_2781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2782_: u8 = 0;
    let mut v_res_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2782_ = (crate::leanh::lean_unbox(v_pu_2774_) as u8);
    v_res_2783_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(v_pu_boxed_2782_, v_v_2775_, v_f_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
    crate::leanh::lean_dec(v___y_2780_);
    crate::leanh::lean_dec_ref(v___y_2779_);
    crate::leanh::lean_dec(v___y_2778_);
    crate::leanh::lean_dec_ref(v___y_2777_);
    return v_res_2783_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(
    mut v_toSignature_2784_: *mut crate::leanh::LeanObject,
    mut v_a_2785_: u8,
    mut v_pu_2786_: u8,
    mut v_code_2787_: *mut crate::leanh::LeanObject,
    mut v___y_2788_: *mut crate::leanh::LeanObject,
    mut v___y_2789_: *mut crate::leanh::LeanObject,
    mut v___y_2790_: *mut crate::leanh::LeanObject,
    mut v___y_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2804_: u8 = 0;
    let mut v_kind_2805_: u8 = 0;
    let mut v___x_2806_: u8 = 0;
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2793_ = lean_st_ref_get(v___y_2791_);
                v_env_2794_ = crate::leanh::lean_ctor_get(v___x_2793_, 0);
                crate::leanh::lean_inc_ref(v_env_2794_);
                crate::leanh::lean_dec(v___x_2793_);
                v_name_2795_ = crate::leanh::lean_ctor_get(v_toSignature_2784_, 0);
                crate::leanh::lean_inc(v_name_2795_);
                crate::leanh::lean_dec_ref(v_toSignature_2784_);
                v___x_2796_ = 1;
                v___x_2797_ = l_Lean_Environment_setExporting(v_env_2794_, v___x_2796_);
                v___x_2798_ =
                    l_Lean_Environment_findAsync_x3f(v___x_2797_, v_name_2795_, v_a_2785_);
                if crate::leanh::lean_obj_tag(v___x_2798_) == 0 {
                    v___x_2799_ = crate::leanh::lean_box((v_a_2785_) as usize);
                    v___x_2800_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2800_, 0, v___x_2799_);
                    return v___x_2800_;
                } else {
                    v_val_2801_ = crate::leanh::lean_ctor_get(v___x_2798_, 0);
                    v_isSharedCheck_2820_ = (!crate::leanh::lean_is_exclusive(v___x_2798_)) as u8;
                    if v_isSharedCheck_2820_ == 0 {
                        v___x_2803_ = v___x_2798_;
                        v_isShared_2804_ = v_isSharedCheck_2820_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2801_);
                        crate::leanh::lean_dec(v___x_2798_);
                        v___x_2803_ = crate::leanh::lean_box(0);
                        v_isShared_2804_ = v_isSharedCheck_2820_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_kind_2805_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_2801_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec(v_val_2801_);
                v___x_2806_ = 0;
                v___x_2807_ = l_Lean_instBEqConstantKind_beq(v_kind_2805_, v___x_2806_);
                if v___x_2807_ == 0 {
                    v___x_2808_ = crate::leanh::lean_box((v___x_2807_) as usize);
                    if v_isShared_2804_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2803_, 0);
                        crate::leanh::lean_ctor_set(v___x_2803_, 0, v___x_2808_);
                        v___x_2810_ = v___x_2803_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2811_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
                        v___x_2810_ = v_reuseFailAlloc_2811_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_options_2812_ = crate::leanh::lean_ctor_get(v___y_2790_, 2);
                    v___x_2813_ = l_Lean_Compiler_LCNF_compiler_small;
                    v___x_2814_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v_options_2812_, v___x_2813_);
                    v___x_2815_ =
                        l_Lean_Compiler_LCNF_Code_sizeLe(v_pu_2786_, v_code_2787_, v___x_2814_);
                    crate::leanh::lean_dec(v___x_2814_);
                    v___x_2816_ = crate::leanh::lean_box((v___x_2815_) as usize);
                    if v_isShared_2804_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2803_, 0);
                        crate::leanh::lean_ctor_set(v___x_2803_, 0, v___x_2816_);
                        v___x_2818_ = v___x_2803_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2816_);
                        v___x_2818_ = v_reuseFailAlloc_2819_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2810_;
            }
            3 => {
                return v___x_2818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed(
    mut v_toSignature_2821_: *mut crate::leanh::LeanObject,
    mut v_a_2822_: *mut crate::leanh::LeanObject,
    mut v_pu_2823_: *mut crate::leanh::LeanObject,
    mut v_code_2824_: *mut crate::leanh::LeanObject,
    mut v___y_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
    mut v___y_2827_: *mut crate::leanh::LeanObject,
    mut v___y_2828_: *mut crate::leanh::LeanObject,
    mut v___y_2829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_951__boxed_2830_: u8 = 0;
    let mut v_pu_boxed_2831_: u8 = 0;
    let mut v_res_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_951__boxed_2830_ = (crate::leanh::lean_unbox(v_a_2822_) as u8);
    v_pu_boxed_2831_ = (crate::leanh::lean_unbox(v_pu_2823_) as u8);
    v_res_2832_ =
        l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(
            v_toSignature_2821_,
            v_a_951__boxed_2830_,
            v_pu_boxed_2831_,
            v_code_2824_,
            v___y_2825_,
            v___y_2826_,
            v___y_2827_,
            v___y_2828_,
        );
    crate::leanh::lean_dec(v___y_2828_);
    crate::leanh::lean_dec_ref(v___y_2827_);
    crate::leanh::lean_dec(v___y_2826_);
    crate::leanh::lean_dec_ref(v___y_2825_);
    crate::leanh::lean_dec_ref(v_code_2824_);
    return v_res_2832_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(
    mut v_pu_2833_: u8,
    mut v_decl_2834_: *mut crate::leanh::LeanObject,
    mut v_a_2835_: *mut crate::leanh::LeanObject,
    mut v_a_2836_: *mut crate::leanh::LeanObject,
    mut v_a_2837_: *mut crate::leanh::LeanObject,
    mut v_a_2838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_decl_2834_);
    v___x_2840_ =
        l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_decl_2834_, v_a_2837_, v_a_2838_);
    if crate::leanh::lean_obj_tag(v___x_2840_) == 0 {
        let mut v_a_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2842_: u8 = 0;
        v_a_2841_ = crate::leanh::lean_ctor_get(v___x_2840_, 0);
        crate::leanh::lean_inc(v_a_2841_);
        v___x_2842_ = (crate::leanh::lean_unbox(v_a_2841_) as u8);
        if v___x_2842_ == 0 {
            let mut v_toSignature_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2840_, 1);
            v_toSignature_2843_ = crate::leanh::lean_ctor_get(v_decl_2834_, 0);
            crate::leanh::lean_inc_ref(v_toSignature_2843_);
            v_value_2844_ = crate::leanh::lean_ctor_get(v_decl_2834_, 1);
            crate::leanh::lean_inc_ref(v_value_2844_);
            crate::leanh::lean_dec_ref(v_decl_2834_);
            v___x_2845_ = crate::leanh::lean_box((v_pu_2833_) as usize);
            v___f_2846_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
            crate::leanh::lean_closure_set(v___f_2846_, 0, v_toSignature_2843_);
            crate::leanh::lean_closure_set(v___f_2846_, 1, v_a_2841_);
            crate::leanh::lean_closure_set(v___f_2846_, 2, v___x_2845_);
            v___x_2847_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_value_2844_, v___f_2846_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_);
            return v___x_2847_;
        } else {
            crate::leanh::lean_dec(v_a_2841_);
            crate::leanh::lean_dec_ref(v_decl_2834_);
            return v___x_2840_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_decl_2834_);
        return v___x_2840_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___boxed(
    mut v_pu_2848_: *mut crate::leanh::LeanObject,
    mut v_decl_2849_: *mut crate::leanh::LeanObject,
    mut v_a_2850_: *mut crate::leanh::LeanObject,
    mut v_a_2851_: *mut crate::leanh::LeanObject,
    mut v_a_2852_: *mut crate::leanh::LeanObject,
    mut v_a_2853_: *mut crate::leanh::LeanObject,
    mut v_a_2854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2855_: u8 = 0;
    let mut v_res_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2855_ = (crate::leanh::lean_unbox(v_pu_2848_) as u8);
    v_res_2856_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(
        v_pu_boxed_2855_,
        v_decl_2849_,
        v_a_2850_,
        v_a_2851_,
        v_a_2852_,
        v_a_2853_,
    );
    crate::leanh::lean_dec(v_a_2853_);
    crate::leanh::lean_dec_ref(v_a_2852_);
    crate::leanh::lean_dec(v_a_2851_);
    crate::leanh::lean_dec_ref(v_a_2850_);
    return v_res_2856_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2857_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2857_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2858_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0,
    );
    v___x_2859_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2859_, 0, v___x_2858_);
    return v___x_2859_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2860_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1,
    );
    v___x_2861_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2862_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2862_, 0, v___x_2861_);
    crate::leanh::lean_ctor_set(v___x_2862_, 1, v___x_2861_);
    crate::leanh::lean_ctor_set(v___x_2862_, 2, v___x_2861_);
    crate::leanh::lean_ctor_set(v___x_2862_, 3, v___x_2861_);
    crate::leanh::lean_ctor_set(v___x_2862_, 4, v___x_2860_);
    crate::leanh::lean_ctor_set(v___x_2862_, 5, v___x_2860_);
    crate::leanh::lean_ctor_set(v___x_2862_, 6, v___x_2860_);
    crate::leanh::lean_ctor_set(v___x_2862_, 7, v___x_2860_);
    crate::leanh::lean_ctor_set(v___x_2862_, 8, v___x_2860_);
    crate::leanh::lean_ctor_set(v___x_2862_, 9, v___x_2860_);
    return v___x_2862_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3()
-> f64 {
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: f64 = 0.0;
    v___x_2863_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2864_ = lean_float_of_nat(v___x_2863_);
    return v___x_2864_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(
    mut v_cls_2868_: *mut crate::leanh::LeanObject,
    mut v_msg_2869_: *mut crate::leanh::LeanObject,
    mut v___y_2870_: *mut crate::leanh::LeanObject,
    mut v___y_2871_: *mut crate::leanh::LeanObject,
    mut v___y_2872_: *mut crate::leanh::LeanObject,
    mut v___y_2873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2883_: u8 = 0;
    let mut v_env_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2888_: u8 = 0;
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v_tid_2903_: u64 = 0;
    let mut v_traces_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2908_: u8 = 0;
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: f64 = 0.0;
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_isSharedCheck_2936_: u8 = 0;
    let mut v_unused_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2938_: u8 = 0;
    let mut v_a_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2942_: u8 = 0;
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2875_ = crate::leanh::lean_ctor_get(v___y_2872_, 2);
                v_ref_2876_ = crate::leanh::lean_ctor_get(v___y_2872_, 5);
                v___x_2877_ = lean_st_ref_get(v___y_2873_);
                v___x_2878_ = lean_st_ref_get(v___y_2871_);
                v___x_2879_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2870_);
                if crate::leanh::lean_obj_tag(v___x_2879_) == 0 {
                    v_a_2880_ = crate::leanh::lean_ctor_get(v___x_2879_, 0);
                    v_isSharedCheck_2938_ = (!crate::leanh::lean_is_exclusive(v___x_2879_)) as u8;
                    if v_isSharedCheck_2938_ == 0 {
                        v___x_2882_ = v___x_2879_;
                        v_isShared_2883_ = v_isSharedCheck_2938_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2880_);
                        crate::leanh::lean_dec(v___x_2879_);
                        v___x_2882_ = crate::leanh::lean_box(0);
                        v_isShared_2883_ = v_isSharedCheck_2938_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2878_);
                    crate::leanh::lean_dec(v___x_2877_);
                    crate::leanh::lean_dec_ref(v_msg_2869_);
                    crate::leanh::lean_dec(v_cls_2868_);
                    v_a_2939_ = crate::leanh::lean_ctor_get(v___x_2879_, 0);
                    v_isSharedCheck_2946_ = (!crate::leanh::lean_is_exclusive(v___x_2879_)) as u8;
                    if v_isSharedCheck_2946_ == 0 {
                        v___x_2941_ = v___x_2879_;
                        v_isShared_2942_ = v_isSharedCheck_2946_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2939_);
                        crate::leanh::lean_dec(v___x_2879_);
                        v___x_2941_ = crate::leanh::lean_box(0);
                        v_isShared_2942_ = v_isSharedCheck_2946_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_2884_ = crate::leanh::lean_ctor_get(v___x_2877_, 0);
                crate::leanh::lean_inc_ref(v_env_2884_);
                crate::leanh::lean_dec(v___x_2877_);
                v_lctx_2885_ = crate::leanh::lean_ctor_get(v___x_2878_, 0);
                v_isSharedCheck_2936_ = (!crate::leanh::lean_is_exclusive(v___x_2878_)) as u8;
                if v_isSharedCheck_2936_ == 0 {
                    v_unused_2937_ = crate::leanh::lean_ctor_get(v___x_2878_, 1);
                    crate::leanh::lean_dec(v_unused_2937_);
                    v___x_2887_ = v___x_2878_;
                    v_isShared_2888_ = v_isSharedCheck_2936_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_2885_);
                    crate::leanh::lean_dec(v___x_2878_);
                    v___x_2887_ = crate::leanh::lean_box(0);
                    v_isShared_2888_ = v_isSharedCheck_2936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2889_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
                v___x_2890_ = lean_st_ref_take(v___y_2873_);
                v_traceState_2891_ = crate::leanh::lean_ctor_get(v___x_2890_, 4);
                v_env_2892_ = crate::leanh::lean_ctor_get(v___x_2890_, 0);
                v_nextMacroScope_2893_ = crate::leanh::lean_ctor_get(v___x_2890_, 1);
                v_ngen_2894_ = crate::leanh::lean_ctor_get(v___x_2890_, 2);
                v_auxDeclNGen_2895_ = crate::leanh::lean_ctor_get(v___x_2890_, 3);
                v_cache_2896_ = crate::leanh::lean_ctor_get(v___x_2890_, 5);
                v_messages_2897_ = crate::leanh::lean_ctor_get(v___x_2890_, 6);
                v_infoState_2898_ = crate::leanh::lean_ctor_get(v___x_2890_, 7);
                v_snapshotTasks_2899_ = crate::leanh::lean_ctor_get(v___x_2890_, 8);
                v_isSharedCheck_2935_ = (!crate::leanh::lean_is_exclusive(v___x_2890_)) as u8;
                if v_isSharedCheck_2935_ == 0 {
                    v___x_2901_ = v___x_2890_;
                    v_isShared_2902_ = v_isSharedCheck_2935_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2899_);
                    crate::leanh::lean_inc(v_infoState_2898_);
                    crate::leanh::lean_inc(v_messages_2897_);
                    crate::leanh::lean_inc(v_cache_2896_);
                    crate::leanh::lean_inc(v_traceState_2891_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2895_);
                    crate::leanh::lean_inc(v_ngen_2894_);
                    crate::leanh::lean_inc(v_nextMacroScope_2893_);
                    crate::leanh::lean_inc(v_env_2892_);
                    crate::leanh::lean_dec(v___x_2890_);
                    v___x_2901_ = crate::leanh::lean_box(0);
                    v_isShared_2902_ = v_isSharedCheck_2935_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_2903_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2891_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2904_ = crate::leanh::lean_ctor_get(v_traceState_2891_, 0);
                v_isSharedCheck_2934_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2891_)) as u8;
                if v_isSharedCheck_2934_ == 0 {
                    v___x_2906_ = v_traceState_2891_;
                    v_isShared_2907_ = v_isSharedCheck_2934_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2904_);
                    crate::leanh::lean_dec(v_traceState_2891_);
                    v___x_2906_ = crate::leanh::lean_box(0);
                    v_isShared_2907_ = v_isSharedCheck_2934_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2908_ = (crate::leanh::lean_unbox(v_a_2880_) as u8);
                crate::leanh::lean_dec(v_a_2880_);
                v___x_2909_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2885_, v___x_2908_);
                crate::leanh::lean_dec_ref(v_lctx_2885_);
                crate::leanh::lean_inc_ref(v_options_2875_);
                v___x_2910_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2910_, 0, v_env_2884_);
                crate::leanh::lean_ctor_set(v___x_2910_, 1, v___x_2889_);
                crate::leanh::lean_ctor_set(v___x_2910_, 2, v___x_2909_);
                crate::leanh::lean_ctor_set(v___x_2910_, 3, v_options_2875_);
                if v_isShared_2888_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2887_, 3);
                    crate::leanh::lean_ctor_set(v___x_2887_, 1, v_msg_2869_);
                    crate::leanh::lean_ctor_set(v___x_2887_, 0, v___x_2910_);
                    v___x_2912_ = v___x_2887_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_msg_2869_);
                    v___x_2912_ = v_reuseFailAlloc_2933_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2913_ = crate::leanh::lean_box(0);
                v___x_2914_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
                v___x_2915_ = 0;
                v___x_2916_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4;
                v___x_2917_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2917_, 0, v_cls_2868_);
                crate::leanh::lean_ctor_set(v___x_2917_, 1, v___x_2913_);
                crate::leanh::lean_ctor_set(v___x_2917_, 2, v___x_2916_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2917_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2914_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2917_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2914_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2917_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2915_,
                );
                v___x_2918_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5;
                v___x_2919_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2919_, 0, v___x_2917_);
                crate::leanh::lean_ctor_set(v___x_2919_, 1, v___x_2912_);
                crate::leanh::lean_ctor_set(v___x_2919_, 2, v___x_2918_);
                crate::leanh::lean_inc(v_ref_2876_);
                v___x_2920_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2920_, 0, v_ref_2876_);
                crate::leanh::lean_ctor_set(v___x_2920_, 1, v___x_2919_);
                v___x_2921_ = l_Lean_PersistentArray_push___redArg(v_traces_2904_, v___x_2920_);
                if v_isShared_2907_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2906_, 0, v___x_2921_);
                    v___x_2923_ = v___x_2906_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2932_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2921_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2932_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2903_,
                    );
                    v___x_2923_ = v_reuseFailAlloc_2932_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2901_, 4, v___x_2923_);
                    v___x_2925_ = v___x_2901_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_env_2892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_nextMacroScope_2893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 2, v_ngen_2894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 3, v_auxDeclNGen_2895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 4, v___x_2923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 5, v_cache_2896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 6, v_messages_2897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 7, v_infoState_2898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 8, v_snapshotTasks_2899_);
                    v___x_2925_ = v_reuseFailAlloc_2931_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2926_ = lean_st_ref_set(v___y_2873_, v___x_2925_);
                v___x_2927_ = crate::leanh::lean_box(0);
                if v_isShared_2883_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2882_, 0, v___x_2927_);
                    v___x_2929_ = v___x_2882_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
                    v___x_2929_ = v_reuseFailAlloc_2930_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2929_;
            }
            9 => {
                if v_isShared_2942_ == 0 {
                    v___x_2944_ = v___x_2941_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
                    v___x_2944_ = v_reuseFailAlloc_2945_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___boxed(
    mut v_cls_2947_: *mut crate::leanh::LeanObject,
    mut v_msg_2948_: *mut crate::leanh::LeanObject,
    mut v___y_2949_: *mut crate::leanh::LeanObject,
    mut v___y_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
    mut v___y_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2954_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(
        v_cls_2947_,
        v_msg_2948_,
        v___y_2949_,
        v___y_2950_,
        v___y_2951_,
        v___y_2952_,
    );
    crate::leanh::lean_dec(v___y_2952_);
    crate::leanh::lean_dec_ref(v___y_2951_);
    crate::leanh::lean_dec(v___y_2950_);
    crate::leanh::lean_dec_ref(v___y_2949_);
    return v_res_2954_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(
    mut v_f_2955_: *mut crate::leanh::LeanObject,
    mut v_v_2956_: *mut crate::leanh::LeanObject,
    mut v___y_2957_: *mut crate::leanh::LeanObject,
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
    mut v___y_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut v_unused_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_2956_) == 0 {
                    v_code_2962_ = crate::leanh::lean_ctor_get(v_v_2956_, 0);
                    crate::leanh::lean_inc_ref(v_code_2962_);
                    crate::leanh::lean_dec_ref_known(v_v_2956_, 1);
                    crate::leanh::lean_inc(v___y_2960_);
                    crate::leanh::lean_inc_ref(v___y_2959_);
                    crate::leanh::lean_inc(v___y_2958_);
                    crate::leanh::lean_inc_ref(v___y_2957_);
                    v___x_2963_ = crate::leanh::lean_apply_6(
                        v_f_2955_,
                        v_code_2962_,
                        v___y_2957_,
                        v___y_2958_,
                        v___y_2959_,
                        v___y_2960_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2963_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_2955_);
                    v_isSharedCheck_2971_ = (!crate::leanh::lean_is_exclusive(v_v_2956_)) as u8;
                    if v_isSharedCheck_2971_ == 0 {
                        v_unused_2972_ = crate::leanh::lean_ctor_get(v_v_2956_, 0);
                        crate::leanh::lean_dec(v_unused_2972_);
                        v___x_2965_ = v_v_2956_;
                        v_isShared_2966_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_2956_);
                        v___x_2965_ = crate::leanh::lean_box(0);
                        v_isShared_2966_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2967_ = crate::leanh::lean_box(0);
                if v_isShared_2966_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2965_, 0);
                    crate::leanh::lean_ctor_set(v___x_2965_, 0, v___x_2967_);
                    v___x_2969_ = v___x_2965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2970_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
                    v___x_2969_ = v_reuseFailAlloc_2970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg___boxed(
    mut v_f_2973_: *mut crate::leanh::LeanObject,
    mut v_v_2974_: *mut crate::leanh::LeanObject,
    mut v___y_2975_: *mut crate::leanh::LeanObject,
    mut v___y_2976_: *mut crate::leanh::LeanObject,
    mut v___y_2977_: *mut crate::leanh::LeanObject,
    mut v___y_2978_: *mut crate::leanh::LeanObject,
    mut v___y_2979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2980_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_2973_, v_v_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
    crate::leanh::lean_dec(v___y_2978_);
    crate::leanh::lean_dec_ref(v___y_2977_);
    crate::leanh::lean_dec(v___y_2976_);
    crate::leanh::lean_dec_ref(v___y_2975_);
    return v_res_2980_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(
    mut v_pu_2981_: u8,
    mut v_f_2982_: *mut crate::leanh::LeanObject,
    mut v_v_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
    mut v___y_2985_: *mut crate::leanh::LeanObject,
    mut v___y_2986_: *mut crate::leanh::LeanObject,
    mut v___y_2987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2989_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_2982_, v_v_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
    return v___x_2989_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___boxed(
    mut v_pu_2990_: *mut crate::leanh::LeanObject,
    mut v_f_2991_: *mut crate::leanh::LeanObject,
    mut v_v_2992_: *mut crate::leanh::LeanObject,
    mut v___y_2993_: *mut crate::leanh::LeanObject,
    mut v___y_2994_: *mut crate::leanh::LeanObject,
    mut v___y_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
    mut v___y_2997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2998_: u8 = 0;
    let mut v_res_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2998_ = (crate::leanh::lean_unbox(v_pu_2990_) as u8);
    v_res_2999_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(v_pu_boxed_2998_, v_f_2991_, v_v_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
    crate::leanh::lean_dec(v___y_2996_);
    crate::leanh::lean_dec_ref(v___y_2995_);
    crate::leanh::lean_dec(v___y_2994_);
    crate::leanh::lean_dec_ref(v___y_2993_);
    return v_res_2999_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3000_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3000_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3001_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once),
        _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0,
    );
    v___x_3002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3002_, 0, v___x_3001_);
    return v___x_3002_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3003_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once),
        _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1,
    );
    v___x_3004_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3004_, 0, v___x_3003_);
    crate::leanh::lean_ctor_set(v___x_3004_, 1, v___x_3003_);
    return v___x_3004_;
}
pub unsafe fn l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed(
    mut v_pu_3005_: *mut crate::leanh::LeanObject,
    mut v_phase_3006_: *mut crate::leanh::LeanObject,
    mut v_decl_3007_: *mut crate::leanh::LeanObject,
    mut v_code_3008_: *mut crate::leanh::LeanObject,
    mut v___y_3009_: *mut crate::leanh::LeanObject,
    mut v___y_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
    mut v___y_3012_: *mut crate::leanh::LeanObject,
    mut v___y_3013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3014_: u8 = 0;
    let mut v_phase_boxed_3015_: u8 = 0;
    let mut v_res_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3014_ = (crate::leanh::lean_unbox(v_pu_3005_) as u8);
    v_phase_boxed_3015_ = (crate::leanh::lean_unbox(v_phase_3006_) as u8);
    v_res_3016_ = l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(
        v_pu_boxed_3014_,
        v_phase_boxed_3015_,
        v_decl_3007_,
        v_code_3008_,
        v___y_3009_,
        v___y_3010_,
        v___y_3011_,
        v___y_3012_,
    );
    crate::leanh::lean_dec(v___y_3012_);
    crate::leanh::lean_dec_ref(v___y_3011_);
    crate::leanh::lean_dec(v___y_3010_);
    crate::leanh::lean_dec_ref(v___y_3009_);
    return v_res_3016_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3025_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2;
    v___x_3026_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4;
    v___x_3027_ = l_Lean_Name_append(v___x_3026_, v___x_3025_);
    return v___x_3027_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3029_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6;
    v___x_3030_ = l_Lean_stringToMessageData(v___x_3029_);
    return v___x_3030_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3;
    v___x_3033_ = l_Lean_stringToMessageData(v___x_3032_);
    return v___x_3033_;
}
pub unsafe fn l_Lean_Compiler_LCNF_markDeclPublicRec(
    mut v_pu_3034_: u8,
    mut v_phase_3035_: u8,
    mut v_decl_3036_: *mut crate::leanh::LeanObject,
    mut v_a_3037_: *mut crate::leanh::LeanObject,
    mut v_a_3038_: *mut crate::leanh::LeanObject,
    mut v_a_3039_: *mut crate::leanh::LeanObject,
    mut v_a_3040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3054_: u8 = 0;
    let mut v_value_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: u8 = 0;
    let mut v_env_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: u8 = 0;
    let mut v_options_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3078_: u8 = 0;
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3098_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3105_: u8 = 0;
    let mut v_unused_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_a_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_reuseFailAlloc_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_unused_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3042_ = lean_st_ref_take(v_a_3040_);
                v_toSignature_3043_ = crate::leanh::lean_ctor_get(v_decl_3036_, 0);
                v_env_3044_ = crate::leanh::lean_ctor_get(v___x_3042_, 0);
                v_nextMacroScope_3045_ = crate::leanh::lean_ctor_get(v___x_3042_, 1);
                v_ngen_3046_ = crate::leanh::lean_ctor_get(v___x_3042_, 2);
                v_auxDeclNGen_3047_ = crate::leanh::lean_ctor_get(v___x_3042_, 3);
                v_traceState_3048_ = crate::leanh::lean_ctor_get(v___x_3042_, 4);
                v_messages_3049_ = crate::leanh::lean_ctor_get(v___x_3042_, 6);
                v_infoState_3050_ = crate::leanh::lean_ctor_get(v___x_3042_, 7);
                v_snapshotTasks_3051_ = crate::leanh::lean_ctor_get(v___x_3042_, 8);
                v_isSharedCheck_3126_ = (!crate::leanh::lean_is_exclusive(v___x_3042_)) as u8;
                if v_isSharedCheck_3126_ == 0 {
                    v_unused_3127_ = crate::leanh::lean_ctor_get(v___x_3042_, 5);
                    crate::leanh::lean_dec(v_unused_3127_);
                    v___x_3053_ = v___x_3042_;
                    v_isShared_3054_ = v_isSharedCheck_3126_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3051_);
                    crate::leanh::lean_inc(v_infoState_3050_);
                    crate::leanh::lean_inc(v_messages_3049_);
                    crate::leanh::lean_inc(v_traceState_3048_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3047_);
                    crate::leanh::lean_inc(v_ngen_3046_);
                    crate::leanh::lean_inc(v_nextMacroScope_3045_);
                    crate::leanh::lean_inc(v_env_3044_);
                    crate::leanh::lean_dec(v___x_3042_);
                    v___x_3053_ = crate::leanh::lean_box(0);
                    v_isShared_3054_ = v_isSharedCheck_3126_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_value_3055_ = crate::leanh::lean_ctor_get(v_decl_3036_, 1);
                crate::leanh::lean_inc_ref(v_value_3055_);
                v_name_3056_ = crate::leanh::lean_ctor_get(v_toSignature_3043_, 0);
                crate::leanh::lean_inc_n(v_name_3056_, 2);
                v___x_3057_ = l_Lean_Compiler_LCNF_setDeclPublic(v_env_3044_, v_name_3056_);
                v___x_3058_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2,
                );
                if v_isShared_3054_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3053_, 5, v___x_3058_);
                    crate::leanh::lean_ctor_set(v___x_3053_, 0, v___x_3057_);
                    v___x_3060_ = v___x_3053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_nextMacroScope_3045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_ngen_3046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 3, v_auxDeclNGen_3047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 4, v_traceState_3048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 5, v___x_3058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 6, v_messages_3049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 7, v_infoState_3050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 8, v_snapshotTasks_3051_);
                    v___x_3060_ = v_reuseFailAlloc_3125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3061_ = lean_st_ref_set(v_a_3040_, v___x_3060_);
                crate::leanh::lean_inc_ref(v_decl_3036_);
                v___x_3062_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_3034_, v_decl_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
                if crate::leanh::lean_obj_tag(v___x_3062_) == 0 {
                    v_a_3063_ = crate::leanh::lean_ctor_get(v___x_3062_, 0);
                    v_isSharedCheck_3116_ = (!crate::leanh::lean_is_exclusive(v___x_3062_)) as u8;
                    if v_isSharedCheck_3116_ == 0 {
                        v___x_3065_ = v___x_3062_;
                        v_isShared_3066_ = v_isSharedCheck_3116_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3063_);
                        crate::leanh::lean_dec(v___x_3062_);
                        v___x_3065_ = crate::leanh::lean_box(0);
                        v_isShared_3066_ = v_isSharedCheck_3116_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_3056_);
                    crate::leanh::lean_dec_ref(v_value_3055_);
                    crate::leanh::lean_dec_ref(v_decl_3036_);
                    v_a_3117_ = crate::leanh::lean_ctor_get(v___x_3062_, 0);
                    v_isSharedCheck_3124_ = (!crate::leanh::lean_is_exclusive(v___x_3062_)) as u8;
                    if v_isSharedCheck_3124_ == 0 {
                        v___x_3119_ = v___x_3062_;
                        v_isShared_3120_ = v_isSharedCheck_3124_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3117_);
                        crate::leanh::lean_dec(v___x_3062_);
                        v___x_3119_ = crate::leanh::lean_box(0);
                        v_isShared_3120_ = v_isSharedCheck_3124_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3067_ = lean_st_ref_get(v_a_3040_);
                v___x_3073_ = (crate::leanh::lean_unbox(v_a_3063_) as u8);
                crate::leanh::lean_dec(v_a_3063_);
                if v___x_3073_ == 0 {
                    crate::leanh::lean_dec(v___x_3067_);
                    crate::leanh::lean_dec(v_name_3056_);
                    crate::leanh::lean_dec_ref(v_value_3055_);
                    crate::leanh::lean_dec_ref(v_decl_3036_);
                    state = 4;
                    continue;
                } else {
                    v_env_3074_ = crate::leanh::lean_ctor_get(v___x_3067_, 0);
                    crate::leanh::lean_inc_ref(v_env_3074_);
                    crate::leanh::lean_dec(v___x_3067_);
                    v___x_3075_ = l_Lean_Compiler_LCNF_isDeclTransparent(
                        v_env_3074_,
                        v_phase_3035_,
                        v_name_3056_,
                    );
                    if v___x_3075_ == 0 {
                        crate::leanh::lean_del_object(v___x_3065_);
                        v_options_3076_ = crate::leanh::lean_ctor_get(v_a_3039_, 2);
                        v_inheritedTraceOptions_3077_ = crate::leanh::lean_ctor_get(v_a_3039_, 13);
                        v_hasTrace_3078_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_3076_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        v___x_3079_ = crate::leanh::lean_box((v_pu_3034_) as usize);
                        v___x_3080_ = crate::leanh::lean_box((v_phase_3035_) as usize);
                        v___f_3081_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed
                                as *mut core::ffi::c_void,
                            9,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_3081_, 0, v___x_3079_);
                        crate::leanh::lean_closure_set(v___f_3081_, 1, v___x_3080_);
                        crate::leanh::lean_closure_set(v___f_3081_, 2, v_decl_3036_);
                        if v_hasTrace_3078_ == 0 {
                            v___y_3083_ = v_a_3037_;
                            v___y_3084_ = v_a_3038_;
                            v___y_3085_ = v_a_3039_;
                            v___y_3086_ = v_a_3040_;
                            state = 6;
                            continue;
                        } else {
                            v___x_3107_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2;
                            v___x_3108_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
                            v___x_3109_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3077_,
                                v_options_3076_,
                                v___x_3108_,
                            );
                            if v___x_3109_ == 0 {
                                v___y_3083_ = v_a_3037_;
                                v___y_3084_ = v_a_3038_;
                                v___y_3085_ = v_a_3039_;
                                v___y_3086_ = v_a_3040_;
                                state = 6;
                                continue;
                            } else {
                                v___x_3110_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
                                crate::leanh::lean_inc(v_name_3056_);
                                v___x_3111_ = l_Lean_MessageData_ofName(v_name_3056_);
                                v___x_3112_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3112_, 0, v___x_3110_);
                                crate::leanh::lean_ctor_set(v___x_3112_, 1, v___x_3111_);
                                v___x_3113_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4_once
                                    ),
                                    _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4,
                                );
                                v___x_3114_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3114_, 0, v___x_3112_);
                                crate::leanh::lean_ctor_set(v___x_3114_, 1, v___x_3113_);
                                v___x_3115_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_3107_, v___x_3114_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
                                if crate::leanh::lean_obj_tag(v___x_3115_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3115_, 1);
                                    v___y_3083_ = v_a_3037_;
                                    v___y_3084_ = v_a_3038_;
                                    v___y_3085_ = v_a_3039_;
                                    v___y_3086_ = v_a_3040_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___f_3081_);
                                    crate::leanh::lean_dec(v_name_3056_);
                                    crate::leanh::lean_dec_ref(v_value_3055_);
                                    return v___x_3115_;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_name_3056_);
                        crate::leanh::lean_dec_ref(v_value_3055_);
                        crate::leanh::lean_dec_ref(v_decl_3036_);
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3069_ = crate::leanh::lean_box(0);
                if v_isShared_3066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3065_, 0, v___x_3069_);
                    v___x_3071_ = v___x_3065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
                    v___x_3071_ = v_reuseFailAlloc_3072_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3071_;
            }
            6 => {
                v___x_3087_ = lean_st_ref_take(v___y_3086_);
                v_env_3088_ = crate::leanh::lean_ctor_get(v___x_3087_, 0);
                v_nextMacroScope_3089_ = crate::leanh::lean_ctor_get(v___x_3087_, 1);
                v_ngen_3090_ = crate::leanh::lean_ctor_get(v___x_3087_, 2);
                v_auxDeclNGen_3091_ = crate::leanh::lean_ctor_get(v___x_3087_, 3);
                v_traceState_3092_ = crate::leanh::lean_ctor_get(v___x_3087_, 4);
                v_messages_3093_ = crate::leanh::lean_ctor_get(v___x_3087_, 6);
                v_infoState_3094_ = crate::leanh::lean_ctor_get(v___x_3087_, 7);
                v_snapshotTasks_3095_ = crate::leanh::lean_ctor_get(v___x_3087_, 8);
                v_isSharedCheck_3105_ = (!crate::leanh::lean_is_exclusive(v___x_3087_)) as u8;
                if v_isSharedCheck_3105_ == 0 {
                    v_unused_3106_ = crate::leanh::lean_ctor_get(v___x_3087_, 5);
                    crate::leanh::lean_dec(v_unused_3106_);
                    v___x_3097_ = v___x_3087_;
                    v_isShared_3098_ = v_isSharedCheck_3105_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3095_);
                    crate::leanh::lean_inc(v_infoState_3094_);
                    crate::leanh::lean_inc(v_messages_3093_);
                    crate::leanh::lean_inc(v_traceState_3092_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3091_);
                    crate::leanh::lean_inc(v_ngen_3090_);
                    crate::leanh::lean_inc(v_nextMacroScope_3089_);
                    crate::leanh::lean_inc(v_env_3088_);
                    crate::leanh::lean_dec(v___x_3087_);
                    v___x_3097_ = crate::leanh::lean_box(0);
                    v_isShared_3098_ = v_isSharedCheck_3105_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3099_ = l_Lean_Compiler_LCNF_setDeclTransparent(
                    v_env_3088_,
                    v_phase_3035_,
                    v_name_3056_,
                );
                if v_isShared_3098_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3097_, 5, v___x_3058_);
                    crate::leanh::lean_ctor_set(v___x_3097_, 0, v___x_3099_);
                    v___x_3101_ = v___x_3097_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3104_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_nextMacroScope_3089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_ngen_3090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_auxDeclNGen_3091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 4, v_traceState_3092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 5, v___x_3058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 6, v_messages_3093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 7, v_infoState_3094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 8, v_snapshotTasks_3095_);
                    v___x_3101_ = v_reuseFailAlloc_3104_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3102_ = lean_st_ref_set(v___y_3086_, v___x_3101_);
                v___x_3103_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v___f_3081_, v_value_3055_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
                return v___x_3103_;
            }
            9 => {
                if v_isShared_3120_ == 0 {
                    v___x_3122_ = v___x_3119_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8;
    v___x_3130_ = l_Lean_stringToMessageData(v___x_3129_);
    return v___x_3130_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(
    mut v_phase_3131_: u8,
    mut v_decl_3132_: *mut crate::leanh::LeanObject,
    mut v_init_3133_: *mut crate::leanh::LeanObject,
    mut v_x_3134_: *mut crate::leanh::LeanObject,
    mut v___y_3135_: *mut crate::leanh::LeanObject,
    mut v___y_3136_: *mut crate::leanh::LeanObject,
    mut v___y_3137_: *mut crate::leanh::LeanObject,
    mut v___y_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: u8 = 0;
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3163_: u8 = 0;
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: u8 = 0;
    let mut v_options_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3168_: u8 = 0;
    let mut v_inheritedTraceOptions_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: u8 = 0;
    let mut v_toSignature_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3186_: u8 = 0;
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3190_: u8 = 0;
    let mut v_a_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3134_) == 0 {
                    v_k_3140_ = crate::leanh::lean_ctor_get(v_x_3134_, 1);
                    crate::leanh::lean_inc(v_k_3140_);
                    v_l_3141_ = crate::leanh::lean_ctor_get(v_x_3134_, 3);
                    crate::leanh::lean_inc(v_l_3141_);
                    v_r_3142_ = crate::leanh::lean_ctor_get(v_x_3134_, 4);
                    crate::leanh::lean_inc(v_r_3142_);
                    crate::leanh::lean_dec_ref_known(v_x_3134_, 5);
                    crate::leanh::lean_inc_ref(v_decl_3132_);
                    v___x_3143_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_3131_, v_decl_3132_, v_init_3133_, v_l_3141_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
                    if crate::leanh::lean_obj_tag(v___x_3143_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3143_, 1);
                        v___x_3144_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(
                            v_k_3140_,
                            v_phase_3131_,
                            v___y_3138_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3144_) == 0 {
                            v_a_3145_ = crate::leanh::lean_ctor_get(v___x_3144_, 0);
                            crate::leanh::lean_inc(v_a_3145_);
                            crate::leanh::lean_dec_ref_known(v___x_3144_, 1);
                            v___x_3146_ = crate::leanh::lean_box(0);
                            if crate::leanh::lean_obj_tag(v_a_3145_) == 1 {
                                v_val_3147_ = crate::leanh::lean_ctor_get(v_a_3145_, 0);
                                crate::leanh::lean_inc(v_val_3147_);
                                crate::leanh::lean_dec_ref_known(v_a_3145_, 1);
                                v___x_3164_ = lean_st_ref_get(v___y_3138_);
                                v_env_3165_ = crate::leanh::lean_ctor_get(v___x_3164_, 0);
                                crate::leanh::lean_inc_ref(v_env_3165_);
                                crate::leanh::lean_dec(v___x_3164_);
                                v___x_3166_ =
                                    l_Lean_Compiler_LCNF_isDeclPublic(v_env_3165_, v_k_3140_);
                                if v___x_3166_ == 0 {
                                    v_options_3167_ = crate::leanh::lean_ctor_get(v___y_3137_, 2);
                                    v_hasTrace_3168_ = crate::leanh::lean_ctor_get_uint8(
                                        v_options_3167_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                            as u32,
                                    );
                                    if v_hasTrace_3168_ == 0 {
                                        crate::leanh::lean_dec(v_k_3140_);
                                        v___y_3149_ = v___y_3135_;
                                        v___y_3150_ = v___y_3136_;
                                        v___y_3151_ = v___y_3137_;
                                        v___y_3152_ = v___y_3138_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_inheritedTraceOptions_3169_ =
                                            crate::leanh::lean_ctor_get(v___y_3137_, 13);
                                        v___x_3170_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2;
                                        v___x_3171_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
                                        v___x_3172_ =
                                            l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                                v_inheritedTraceOptions_3169_,
                                                v_options_3167_,
                                                v___x_3171_,
                                            );
                                        if v___x_3172_ == 0 {
                                            crate::leanh::lean_dec(v_k_3140_);
                                            v___y_3149_ = v___y_3135_;
                                            v___y_3150_ = v___y_3136_;
                                            v___y_3151_ = v___y_3137_;
                                            v___y_3152_ = v___y_3138_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_toSignature_3173_ =
                                                crate::leanh::lean_ctor_get(v_decl_3132_, 0);
                                            v_name_3174_ =
                                                crate::leanh::lean_ctor_get(v_toSignature_3173_, 0);
                                            v___x_3175_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
                                            v___x_3176_ = l_Lean_MessageData_ofName(v_k_3140_);
                                            v___x_3177_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3177_,
                                                0,
                                                v___x_3175_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3177_,
                                                1,
                                                v___x_3176_,
                                            );
                                            v___x_3178_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9);
                                            v___x_3179_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3179_,
                                                0,
                                                v___x_3177_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3179_,
                                                1,
                                                v___x_3178_,
                                            );
                                            crate::leanh::lean_inc(v_name_3174_);
                                            v___x_3180_ = l_Lean_MessageData_ofName(v_name_3174_);
                                            v___x_3181_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3181_,
                                                0,
                                                v___x_3179_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3181_,
                                                1,
                                                v___x_3180_,
                                            );
                                            v___x_3182_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_3170_, v___x_3181_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
                                            if crate::leanh::lean_obj_tag(v___x_3182_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_3182_, 1);
                                                v___y_3149_ = v___y_3135_;
                                                v___y_3150_ = v___y_3136_;
                                                v___y_3151_ = v___y_3137_;
                                                v___y_3152_ = v___y_3138_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_val_3147_);
                                                crate::leanh::lean_dec(v_r_3142_);
                                                crate::leanh::lean_dec_ref(v_decl_3132_);
                                                v_a_3183_ =
                                                    crate::leanh::lean_ctor_get(v___x_3182_, 0);
                                                v_isSharedCheck_3190_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3182_))
                                                        as u8;
                                                if v_isSharedCheck_3190_ == 0 {
                                                    v___x_3185_ = v___x_3182_;
                                                    v_isShared_3186_ = v_isSharedCheck_3190_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3183_);
                                                    crate::leanh::lean_dec(v___x_3182_);
                                                    v___x_3185_ = crate::leanh::lean_box(0);
                                                    v_isShared_3186_ = v_isSharedCheck_3190_;
                                                    state = 4;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_val_3147_);
                                    crate::leanh::lean_dec(v_k_3140_);
                                    v_init_3133_ = v___x_3146_;
                                    v_x_3134_ = v_r_3142_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3145_);
                                crate::leanh::lean_dec(v_k_3140_);
                                v_init_3133_ = v___x_3146_;
                                v_x_3134_ = v_r_3142_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_r_3142_);
                            crate::leanh::lean_dec(v_k_3140_);
                            crate::leanh::lean_dec_ref(v_decl_3132_);
                            v_a_3193_ = crate::leanh::lean_ctor_get(v___x_3144_, 0);
                            v_isSharedCheck_3200_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3144_)) as u8;
                            if v_isSharedCheck_3200_ == 0 {
                                v___x_3195_ = v___x_3144_;
                                v_isShared_3196_ = v_isSharedCheck_3200_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3193_);
                                crate::leanh::lean_dec(v___x_3144_);
                                v___x_3195_ = crate::leanh::lean_box(0);
                                v_isShared_3196_ = v_isSharedCheck_3200_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_3142_);
                        crate::leanh::lean_dec(v_k_3140_);
                        crate::leanh::lean_dec_ref(v_decl_3132_);
                        return v___x_3143_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decl_3132_);
                    v___x_3201_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3201_, 0, v_init_3133_);
                    v___x_3202_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3202_, 0, v___x_3201_);
                    return v___x_3202_;
                }
            }
            1 => {
                v___x_3153_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_3131_);
                v___x_3154_ = l_Lean_Compiler_LCNF_markDeclPublicRec(
                    v___x_3153_,
                    v_phase_3131_,
                    v_val_3147_,
                    v___y_3149_,
                    v___y_3150_,
                    v___y_3151_,
                    v___y_3152_,
                );
                if crate::leanh::lean_obj_tag(v___x_3154_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3154_, 1);
                    v_init_3133_ = v___x_3146_;
                    v_x_3134_ = v_r_3142_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_3142_);
                    crate::leanh::lean_dec_ref(v_decl_3132_);
                    v_a_3156_ = crate::leanh::lean_ctor_get(v___x_3154_, 0);
                    v_isSharedCheck_3163_ = (!crate::leanh::lean_is_exclusive(v___x_3154_)) as u8;
                    if v_isSharedCheck_3163_ == 0 {
                        v___x_3158_ = v___x_3154_;
                        v_isShared_3159_ = v_isSharedCheck_3163_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3156_);
                        crate::leanh::lean_dec(v___x_3154_);
                        v___x_3158_ = crate::leanh::lean_box(0);
                        v_isShared_3159_ = v_isSharedCheck_3163_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3159_ == 0 {
                    v___x_3161_ = v___x_3158_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
                    v___x_3161_ = v_reuseFailAlloc_3162_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3161_;
            }
            4 => {
                if v_isShared_3186_ == 0 {
                    v___x_3188_ = v___x_3185_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
                    v___x_3188_ = v_reuseFailAlloc_3189_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3188_;
            }
            6 => {
                if v_isShared_3196_ == 0 {
                    v___x_3198_ = v___x_3195_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3199_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
                    v___x_3198_ = v_reuseFailAlloc_3199_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0(
    mut v_pu_3203_: u8,
    mut v_phase_3204_: u8,
    mut v_decl_3205_: *mut crate::leanh::LeanObject,
    mut v_code_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
    mut v___y_3209_: *mut crate::leanh::LeanObject,
    mut v___y_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3218_: u8 = 0;
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut v_unused_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3227_: u8 = 0;
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3212_ = l_Lean_NameSet_empty;
                v___x_3213_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_3203_, v_code_3206_, v___x_3212_);
                v___x_3214_ = crate::leanh::lean_box(0);
                v___x_3215_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_3204_, v_decl_3205_, v___x_3214_, v___x_3213_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
                if crate::leanh::lean_obj_tag(v___x_3215_) == 0 {
                    v_isSharedCheck_3222_ = (!crate::leanh::lean_is_exclusive(v___x_3215_)) as u8;
                    if v_isSharedCheck_3222_ == 0 {
                        v_unused_3223_ = crate::leanh::lean_ctor_get(v___x_3215_, 0);
                        crate::leanh::lean_dec(v_unused_3223_);
                        v___x_3217_ = v___x_3215_;
                        v_isShared_3218_ = v_isSharedCheck_3222_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3215_);
                        v___x_3217_ = crate::leanh::lean_box(0);
                        v_isShared_3218_ = v_isSharedCheck_3222_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3224_ = crate::leanh::lean_ctor_get(v___x_3215_, 0);
                    v_isSharedCheck_3231_ = (!crate::leanh::lean_is_exclusive(v___x_3215_)) as u8;
                    if v_isSharedCheck_3231_ == 0 {
                        v___x_3226_ = v___x_3215_;
                        v_isShared_3227_ = v_isSharedCheck_3231_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3224_);
                        crate::leanh::lean_dec(v___x_3215_);
                        v___x_3226_ = crate::leanh::lean_box(0);
                        v_isShared_3227_ = v_isSharedCheck_3231_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3218_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3217_, 0, v___x_3214_);
                    v___x_3220_ = v___x_3217_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3214_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3220_;
            }
            3 => {
                if v_isShared_3227_ == 0 {
                    v___x_3229_ = v___x_3226_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
                    v___x_3229_ = v_reuseFailAlloc_3230_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___boxed(
    mut v_phase_3232_: *mut crate::leanh::LeanObject,
    mut v_decl_3233_: *mut crate::leanh::LeanObject,
    mut v_init_3234_: *mut crate::leanh::LeanObject,
    mut v_x_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_3241_: u8 = 0;
    let mut v_res_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_3241_ = (crate::leanh::lean_unbox(v_phase_3232_) as u8);
    v_res_3242_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_boxed_3241_, v_decl_3233_, v_init_3234_, v_x_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
    crate::leanh::lean_dec(v___y_3239_);
    crate::leanh::lean_dec_ref(v___y_3238_);
    crate::leanh::lean_dec(v___y_3237_);
    crate::leanh::lean_dec_ref(v___y_3236_);
    return v_res_3242_;
}
pub unsafe fn l_Lean_Compiler_LCNF_markDeclPublicRec___boxed(
    mut v_pu_3243_: *mut crate::leanh::LeanObject,
    mut v_phase_3244_: *mut crate::leanh::LeanObject,
    mut v_decl_3245_: *mut crate::leanh::LeanObject,
    mut v_a_3246_: *mut crate::leanh::LeanObject,
    mut v_a_3247_: *mut crate::leanh::LeanObject,
    mut v_a_3248_: *mut crate::leanh::LeanObject,
    mut v_a_3249_: *mut crate::leanh::LeanObject,
    mut v_a_3250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3251_: u8 = 0;
    let mut v_phase_boxed_3252_: u8 = 0;
    let mut v_res_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3251_ = (crate::leanh::lean_unbox(v_pu_3243_) as u8);
    v_phase_boxed_3252_ = (crate::leanh::lean_unbox(v_phase_3244_) as u8);
    v_res_3253_ = l_Lean_Compiler_LCNF_markDeclPublicRec(
        v_pu_boxed_3251_,
        v_phase_boxed_3252_,
        v_decl_3245_,
        v_a_3246_,
        v_a_3247_,
        v_a_3248_,
        v_a_3249_,
    );
    crate::leanh::lean_dec(v_a_3249_);
    crate::leanh::lean_dec_ref(v_a_3248_);
    crate::leanh::lean_dec(v_a_3247_);
    crate::leanh::lean_dec_ref(v_a_3246_);
    return v_res_3253_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(
    mut v_msg_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
    mut v___y_3256_: *mut crate::leanh::LeanObject,
    mut v___y_3257_: *mut crate::leanh::LeanObject,
    mut v___y_3258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v_env_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3274_: u8 = 0;
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v_unused_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_a_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3260_ = crate::leanh::lean_ctor_get(v___y_3257_, 2);
                v_ref_3261_ = crate::leanh::lean_ctor_get(v___y_3257_, 5);
                v___x_3262_ = lean_st_ref_get(v___y_3258_);
                v___x_3263_ = lean_st_ref_get(v___y_3256_);
                v___x_3264_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3255_);
                if crate::leanh::lean_obj_tag(v___x_3264_) == 0 {
                    v_a_3265_ = crate::leanh::lean_ctor_get(v___x_3264_, 0);
                    v_isSharedCheck_3287_ = (!crate::leanh::lean_is_exclusive(v___x_3264_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v___x_3267_ = v___x_3264_;
                        v_isShared_3268_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3265_);
                        crate::leanh::lean_dec(v___x_3264_);
                        v___x_3267_ = crate::leanh::lean_box(0);
                        v_isShared_3268_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3263_);
                    crate::leanh::lean_dec(v___x_3262_);
                    crate::leanh::lean_dec_ref(v_msg_3254_);
                    v_a_3288_ = crate::leanh::lean_ctor_get(v___x_3264_, 0);
                    v_isSharedCheck_3295_ = (!crate::leanh::lean_is_exclusive(v___x_3264_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3290_ = v___x_3264_;
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3288_);
                        crate::leanh::lean_dec(v___x_3264_);
                        v___x_3290_ = crate::leanh::lean_box(0);
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_3269_ = crate::leanh::lean_ctor_get(v___x_3262_, 0);
                crate::leanh::lean_inc_ref(v_env_3269_);
                crate::leanh::lean_dec(v___x_3262_);
                v_lctx_3270_ = crate::leanh::lean_ctor_get(v___x_3263_, 0);
                v_isSharedCheck_3285_ = (!crate::leanh::lean_is_exclusive(v___x_3263_)) as u8;
                if v_isSharedCheck_3285_ == 0 {
                    v_unused_3286_ = crate::leanh::lean_ctor_get(v___x_3263_, 1);
                    crate::leanh::lean_dec(v_unused_3286_);
                    v___x_3272_ = v___x_3263_;
                    v_isShared_3273_ = v_isSharedCheck_3285_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_3270_);
                    crate::leanh::lean_dec(v___x_3263_);
                    v___x_3272_ = crate::leanh::lean_box(0);
                    v_isShared_3273_ = v_isSharedCheck_3285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3274_ = (crate::leanh::lean_unbox(v_a_3265_) as u8);
                crate::leanh::lean_dec(v_a_3265_);
                v___x_3275_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3270_, v___x_3274_);
                crate::leanh::lean_dec_ref(v_lctx_3270_);
                v___x_3276_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
                crate::leanh::lean_inc_ref(v_options_3260_);
                v___x_3277_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3277_, 0, v_env_3269_);
                crate::leanh::lean_ctor_set(v___x_3277_, 1, v___x_3276_);
                crate::leanh::lean_ctor_set(v___x_3277_, 2, v___x_3275_);
                crate::leanh::lean_ctor_set(v___x_3277_, 3, v_options_3260_);
                if v_isShared_3273_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3272_, 3);
                    crate::leanh::lean_ctor_set(v___x_3272_, 1, v_msg_3254_);
                    crate::leanh::lean_ctor_set(v___x_3272_, 0, v___x_3277_);
                    v___x_3279_ = v___x_3272_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_msg_3254_);
                    v___x_3279_ = v_reuseFailAlloc_3284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_ref_3261_);
                v___x_3280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3280_, 0, v_ref_3261_);
                crate::leanh::lean_ctor_set(v___x_3280_, 1, v___x_3279_);
                if v_isShared_3268_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3267_, 1);
                    crate::leanh::lean_ctor_set(v___x_3267_, 0, v___x_3280_);
                    v___x_3282_ = v___x_3267_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
                    v___x_3282_ = v_reuseFailAlloc_3283_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3282_;
            }
            5 => {
                if v_isShared_3291_ == 0 {
                    v___x_3293_ = v___x_3290_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
                    v___x_3293_ = v_reuseFailAlloc_3294_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg___boxed(
    mut v_msg_3296_: *mut crate::leanh::LeanObject,
    mut v___y_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
    mut v___y_3299_: *mut crate::leanh::LeanObject,
    mut v___y_3300_: *mut crate::leanh::LeanObject,
    mut v___y_3301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3302_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
    crate::leanh::lean_dec(v___y_3300_);
    crate::leanh::lean_dec_ref(v___y_3299_);
    crate::leanh::lean_dec(v___y_3298_);
    crate::leanh::lean_dec_ref(v___y_3297_);
    return v_res_3302_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(
    mut v_00_u03b1_3303_: *mut crate::leanh::LeanObject,
    mut v_msg_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
    mut v___y_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
    mut v___y_3309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_3304_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
    return v___x_3311_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___boxed(
    mut v_00_u03b1_3312_: *mut crate::leanh::LeanObject,
    mut v_msg_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
    mut v___y_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
    mut v___y_3318_: *mut crate::leanh::LeanObject,
    mut v___y_3319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(v_00_u03b1_3312_, v_msg_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
    crate::leanh::lean_dec(v___y_3318_);
    crate::leanh::lean_dec_ref(v___y_3317_);
    crate::leanh::lean_dec(v___y_3316_);
    crate::leanh::lean_dec_ref(v___y_3315_);
    crate::leanh::lean_dec(v___y_3314_);
    return v_res_3320_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(
    mut v_opts_3321_: *mut crate::leanh::LeanObject,
    mut v_opt_3322_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3323_ = crate::leanh::lean_ctor_get(v_opt_3322_, 0);
    v_defValue_3324_ = crate::leanh::lean_ctor_get(v_opt_3322_, 1);
    v_map_3325_ = crate::leanh::lean_ctor_get(v_opts_3321_, 0);
    v___x_3326_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3325_,
            v_name_3323_,
        );
    if crate::leanh::lean_obj_tag(v___x_3326_) == 0 {
        let mut v___x_3327_: u8 = 0;
        v___x_3327_ = (crate::leanh::lean_unbox(v_defValue_3324_) as u8);
        return v___x_3327_;
    } else {
        let mut v_val_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3328_ = crate::leanh::lean_ctor_get(v___x_3326_, 0);
        crate::leanh::lean_inc(v_val_3328_);
        crate::leanh::lean_dec_ref_known(v___x_3326_, 1);
        if crate::leanh::lean_obj_tag(v_val_3328_) == 1 {
            let mut v_v_3329_: u8 = 0;
            v_v_3329_ = crate::leanh::lean_ctor_get_uint8(v_val_3328_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3328_, 0);
            return v_v_3329_;
        } else {
            let mut v___x_3330_: u8 = 0;
            crate::leanh::lean_dec(v_val_3328_);
            v___x_3330_ = (crate::leanh::lean_unbox(v_defValue_3324_) as u8);
            return v___x_3330_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1___boxed(
    mut v_opts_3331_: *mut crate::leanh::LeanObject,
    mut v_opt_3332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3333_: u8 = 0;
    let mut v_r_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_opts_3331_, v_opt_3332_);
    crate::leanh::lean_dec_ref(v_opt_3332_);
    crate::leanh::lean_dec_ref(v_opts_3331_);
    v_r_3334_ = crate::leanh::lean_box((v_res_3333_) as usize);
    return v_r_3334_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(
    mut v_f_3335_: *mut crate::leanh::LeanObject,
    mut v_v_3336_: *mut crate::leanh::LeanObject,
    mut v___y_3337_: *mut crate::leanh::LeanObject,
    mut v___y_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
    mut v___y_3340_: *mut crate::leanh::LeanObject,
    mut v___y_3341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3347_: u8 = 0;
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3353_: u8 = 0;
    let mut v_unused_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_3336_) == 0 {
                    v_code_3343_ = crate::leanh::lean_ctor_get(v_v_3336_, 0);
                    crate::leanh::lean_inc_ref(v_code_3343_);
                    crate::leanh::lean_dec_ref_known(v_v_3336_, 1);
                    crate::leanh::lean_inc(v___y_3341_);
                    crate::leanh::lean_inc_ref(v___y_3340_);
                    crate::leanh::lean_inc(v___y_3339_);
                    crate::leanh::lean_inc_ref(v___y_3338_);
                    v___x_3344_ = crate::leanh::lean_apply_7(
                        v_f_3335_,
                        v_code_3343_,
                        v___y_3337_,
                        v___y_3338_,
                        v___y_3339_,
                        v___y_3340_,
                        v___y_3341_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3344_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_3335_);
                    v_isSharedCheck_3353_ = (!crate::leanh::lean_is_exclusive(v_v_3336_)) as u8;
                    if v_isSharedCheck_3353_ == 0 {
                        v_unused_3354_ = crate::leanh::lean_ctor_get(v_v_3336_, 0);
                        crate::leanh::lean_dec(v_unused_3354_);
                        v___x_3346_ = v_v_3336_;
                        v_isShared_3347_ = v_isSharedCheck_3353_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_3336_);
                        v___x_3346_ = crate::leanh::lean_box(0);
                        v_isShared_3347_ = v_isSharedCheck_3353_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3348_ = crate::leanh::lean_box(0);
                v___x_3349_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3349_, 0, v___x_3348_);
                crate::leanh::lean_ctor_set(v___x_3349_, 1, v___y_3337_);
                if v_isShared_3347_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3346_, 0);
                    crate::leanh::lean_ctor_set(v___x_3346_, 0, v___x_3349_);
                    v___x_3351_ = v___x_3346_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3352_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
                    v___x_3351_ = v_reuseFailAlloc_3352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg___boxed(
    mut v_f_3355_: *mut crate::leanh::LeanObject,
    mut v_v_3356_: *mut crate::leanh::LeanObject,
    mut v___y_3357_: *mut crate::leanh::LeanObject,
    mut v___y_3358_: *mut crate::leanh::LeanObject,
    mut v___y_3359_: *mut crate::leanh::LeanObject,
    mut v___y_3360_: *mut crate::leanh::LeanObject,
    mut v___y_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_3355_, v_v_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
    crate::leanh::lean_dec(v___y_3361_);
    crate::leanh::lean_dec_ref(v___y_3360_);
    crate::leanh::lean_dec(v___y_3359_);
    crate::leanh::lean_dec_ref(v___y_3358_);
    return v_res_3363_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(
    mut v_pu_3364_: u8,
    mut v_f_3365_: *mut crate::leanh::LeanObject,
    mut v_v_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3373_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_3365_, v_v_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
    return v___x_3373_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___boxed(
    mut v_pu_3374_: *mut crate::leanh::LeanObject,
    mut v_f_3375_: *mut crate::leanh::LeanObject,
    mut v_v_3376_: *mut crate::leanh::LeanObject,
    mut v___y_3377_: *mut crate::leanh::LeanObject,
    mut v___y_3378_: *mut crate::leanh::LeanObject,
    mut v___y_3379_: *mut crate::leanh::LeanObject,
    mut v___y_3380_: *mut crate::leanh::LeanObject,
    mut v___y_3381_: *mut crate::leanh::LeanObject,
    mut v___y_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3383_: u8 = 0;
    let mut v_res_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3383_ = (crate::leanh::lean_unbox(v_pu_3374_) as u8);
    v_res_3384_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(v_pu_boxed_3383_, v_f_3375_, v_v_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
    crate::leanh::lean_dec(v___y_3381_);
    crate::leanh::lean_dec_ref(v___y_3380_);
    crate::leanh::lean_dec(v___y_3379_);
    crate::leanh::lean_dec_ref(v___y_3378_);
    return v_res_3384_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3386_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0;
    v___x_3387_ = l_Lean_stringToMessageData(v___x_3386_);
    return v___x_3387_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3389_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2;
    v___x_3390_ = l_Lean_stringToMessageData(v___x_3389_);
    return v___x_3390_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3392_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4;
    v___x_3393_ = l_Lean_stringToMessageData(v___x_3392_);
    return v___x_3393_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3395_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6;
    v___x_3396_ = l_Lean_stringToMessageData(v___x_3395_);
    return v___x_3396_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3398_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8;
    v___x_3399_ = l_Lean_stringToMessageData(v___x_3398_);
    return v___x_3399_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10;
    v___x_3402_ = l_Lean_stringToMessageData(v___x_3401_);
    return v___x_3402_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3404_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12;
    v___x_3405_ = l_Lean_stringToMessageData(v___x_3404_);
    return v___x_3405_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14;
    v___x_3408_ = l_Lean_stringToMessageData(v___x_3407_);
    return v___x_3408_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3410_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16;
    v___x_3411_ = l_Lean_stringToMessageData(v___x_3410_);
    return v___x_3411_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3413_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18;
    v___x_3414_ = l_Lean_stringToMessageData(v___x_3413_);
    return v___x_3414_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3416_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20;
    v___x_3417_ = l_Lean_stringToMessageData(v___x_3416_);
    return v___x_3417_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(
    mut v_pu_3418_: u8,
    mut v_origDecl_3419_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3420_: u8,
    mut v_isPublic_3421_: u8,
    mut v_init_3422_: *mut crate::leanh::LeanObject,
    mut v_x_3423_: *mut crate::leanh::LeanObject,
    mut v___y_3424_: *mut crate::leanh::LeanObject,
    mut v___y_3425_: *mut crate::leanh::LeanObject,
    mut v___y_3426_: *mut crate::leanh::LeanObject,
    mut v___y_3427_: *mut crate::leanh::LeanObject,
    mut v___y_3428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: u8 = 0;
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3466_: u8 = 0;
    let mut v_a_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut v_a_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3479_: u8 = 0;
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3483_: u8 = 0;
    let mut v___y_3485_: u8 = 0;
    let mut v___y_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: u8 = 0;
    let mut v___x_3492_: u8 = 0;
    let mut v___x_3494_: u8 = 0;
    let mut v___x_3496_: u8 = 0;
    let mut v___y_3498_: u8 = 0;
    let mut v___y_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3519_: u8 = 0;
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3523_: u8 = 0;
    let mut v_reuseFailAlloc_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3533_: u8 = 0;
    let mut v_toSignature_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3557_: u8 = 0;
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3561_: u8 = 0;
    let mut v___y_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3567_: u8 = 0;
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___y_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3577_: u8 = 0;
    let mut v___x_3578_: u8 = 0;
    let mut v___x_3579_: u8 = 0;
    let mut v___y_3581_: u8 = 0;
    let mut v___y_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: u8 = 0;
    let mut v___y_3589_: u8 = 0;
    let mut v___y_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3596_: u8 = 0;
    let mut v___y_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3602_: u8 = 0;
    let mut v___x_3603_: u8 = 0;
    let mut v___x_3604_: u8 = 0;
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3630_: u8 = 0;
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3634_: u8 = 0;
    let mut v_toSignature_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3650_: u8 = 0;
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3654_: u8 = 0;
    let mut v___y_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3661_: u8 = 0;
    let mut v___x_3662_: u8 = 0;
    let mut v___y_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: u8 = 0;
    let mut v___x_3672_: u8 = 0;
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: u8 = 0;
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3701_: u8 = 0;
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3705_: u8 = 0;
    let mut v___y_3707_: u8 = 0;
    let mut v_modules_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: u8 = 0;
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExported_3713_: u8 = 0;
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3716_: u8 = 0;
    let mut v_toSignature_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3739_: u8 = 0;
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v_modules_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: u8 = 0;
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExported_3749_: u8 = 0;
    let mut v_isSharedCheck_3751_: u8 = 0;
    let mut v_unused_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3423_) == 0 {
                    v_k_3430_ = crate::leanh::lean_ctor_get(v_x_3423_, 1);
                    crate::leanh::lean_inc(v_k_3430_);
                    v_l_3431_ = crate::leanh::lean_ctor_get(v_x_3423_, 3);
                    crate::leanh::lean_inc(v_l_3431_);
                    v_r_3432_ = crate::leanh::lean_ctor_get(v_x_3423_, 4);
                    crate::leanh::lean_inc(v_r_3432_);
                    crate::leanh::lean_dec_ref_known(v_x_3423_, 5);
                    crate::leanh::lean_inc_ref(v_origDecl_3419_);
                    v___x_3433_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_3418_, v_origDecl_3419_, v_isMeta_3420_, v_isPublic_3421_, v_init_3422_, v_l_3431_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
                    if crate::leanh::lean_obj_tag(v___x_3433_) == 0 {
                        v_a_3434_ = crate::leanh::lean_ctor_get(v___x_3433_, 0);
                        crate::leanh::lean_inc(v_a_3434_);
                        crate::leanh::lean_dec_ref_known(v___x_3433_, 1);
                        v_snd_3435_ = crate::leanh::lean_ctor_get(v_a_3434_, 1);
                        v_isSharedCheck_3751_ = (!crate::leanh::lean_is_exclusive(v_a_3434_)) as u8;
                        if v_isSharedCheck_3751_ == 0 {
                            v_unused_3752_ = crate::leanh::lean_ctor_get(v_a_3434_, 0);
                            crate::leanh::lean_dec(v_unused_3752_);
                            v___x_3437_ = v_a_3434_;
                            v_isShared_3438_ = v_isSharedCheck_3751_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3435_);
                            crate::leanh::lean_dec(v_a_3434_);
                            v___x_3437_ = crate::leanh::lean_box(0);
                            v_isShared_3438_ = v_isSharedCheck_3751_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_3432_);
                        crate::leanh::lean_dec(v_k_3430_);
                        crate::leanh::lean_dec_ref(v_origDecl_3419_);
                        return v___x_3433_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origDecl_3419_);
                    v___x_3753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3753_, 0, v_init_3422_);
                    v___x_3754_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3754_, 0, v___x_3753_);
                    crate::leanh::lean_ctor_set(v___x_3754_, 1, v___y_3424_);
                    v___x_3755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3755_, 0, v___x_3754_);
                    return v___x_3755_;
                }
            }
            1 => {
                v___x_3439_ = crate::leanh::lean_box(0);
                v___x_3496_ = l_Lean_NameSet_contains(v_snd_3435_, v_k_3430_);
                if v___x_3496_ == 0 {
                    v___x_3525_ = lean_st_ref_get(v___y_3428_);
                    v_env_3526_ = crate::leanh::lean_ctor_get(v___x_3525_, 0);
                    crate::leanh::lean_inc_ref(v_env_3526_);
                    crate::leanh::lean_dec(v___x_3525_);
                    crate::leanh::lean_inc(v_k_3430_);
                    v___x_3673_ = l_Lean_NameSet_insert(v_snd_3435_, v_k_3430_);
                    if v_isMeta_3420_ == 0 {
                        v___y_3664_ = v___x_3673_;
                        v___y_3665_ = v___y_3425_;
                        v___y_3666_ = v___y_3426_;
                        v___y_3667_ = v___y_3427_;
                        v___y_3668_ = v___y_3428_;
                        state = 27;
                        continue;
                    } else {
                        if v_isPublic_3421_ == 0 {
                            v___y_3664_ = v___x_3673_;
                            v___y_3665_ = v___y_3425_;
                            v___y_3666_ = v___y_3426_;
                            v___y_3667_ = v___y_3427_;
                            v___y_3668_ = v___y_3428_;
                            state = 27;
                            continue;
                        } else {
                            v___x_3674_ =
                                l_Lean_Environment_getModuleIdxFor_x3f(v_env_3526_, v_k_3430_);
                            if crate::leanh::lean_obj_tag(v___x_3674_) == 1 {
                                v_val_3675_ = crate::leanh::lean_ctor_get(v___x_3674_, 0);
                                crate::leanh::lean_inc(v_val_3675_);
                                crate::leanh::lean_dec_ref_known(v___x_3674_, 1);
                                crate::leanh::lean_inc(v_k_3430_);
                                crate::leanh::lean_inc_ref(v_env_3526_);
                                v___x_3676_ = l_Lean_isMarkedMeta(v_env_3526_, v_k_3430_);
                                if v___x_3676_ == 0 {
                                    v___x_3677_ = l_Lean_Environment_header(v_env_3526_);
                                    v_modules_3708_ = crate::leanh::lean_ctor_get(v___x_3677_, 3);
                                    crate::leanh::lean_inc_ref(v_modules_3708_);
                                    v___x_3709_ = lean_array_get_size(v_modules_3708_);
                                    v___x_3710_ = lean_nat_dec_lt(v_val_3675_, v___x_3709_);
                                    if v___x_3710_ == 0 {
                                        crate::leanh::lean_dec_ref(v_modules_3708_);
                                        v___y_3707_ = v___x_3676_;
                                        state = 31;
                                        continue;
                                    } else {
                                        v___x_3711_ = lean_array_fget(v_modules_3708_, v_val_3675_);
                                        crate::leanh::lean_dec_ref(v_modules_3708_);
                                        v_toImport_3712_ =
                                            crate::leanh::lean_ctor_get(v___x_3711_, 0);
                                        crate::leanh::lean_inc_ref(v_toImport_3712_);
                                        crate::leanh::lean_dec(v___x_3711_);
                                        v_isExported_3713_ = crate::leanh::lean_ctor_get_uint8(
                                            v_toImport_3712_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 1
                                                + 1)
                                                as u32,
                                        );
                                        crate::leanh::lean_dec_ref(v_toImport_3712_);
                                        if v_isExported_3713_ == 0 {
                                            crate::leanh::lean_dec(v___x_3673_);
                                            crate::leanh::lean_dec_ref(v_env_3526_);
                                            crate::leanh::lean_del_object(v___x_3437_);
                                            crate::leanh::lean_dec(v_r_3432_);
                                            state = 28;
                                            continue;
                                        } else {
                                            v___y_3707_ = v___x_3676_;
                                            state = 31;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___x_3714_ = l_Lean_Environment_header(v_env_3526_);
                                    v_modules_3744_ = crate::leanh::lean_ctor_get(v___x_3714_, 3);
                                    crate::leanh::lean_inc_ref(v_modules_3744_);
                                    v___x_3745_ = lean_array_get_size(v_modules_3744_);
                                    v___x_3746_ = lean_nat_dec_lt(v_val_3675_, v___x_3745_);
                                    if v___x_3746_ == 0 {
                                        crate::leanh::lean_dec_ref(v_modules_3744_);
                                        v___y_3716_ = v___x_3496_;
                                        state = 32;
                                        continue;
                                    } else {
                                        v___x_3747_ = lean_array_fget(v_modules_3744_, v_val_3675_);
                                        crate::leanh::lean_dec_ref(v_modules_3744_);
                                        v_toImport_3748_ =
                                            crate::leanh::lean_ctor_get(v___x_3747_, 0);
                                        crate::leanh::lean_inc_ref(v_toImport_3748_);
                                        crate::leanh::lean_dec(v___x_3747_);
                                        v_isExported_3749_ = crate::leanh::lean_ctor_get_uint8(
                                            v_toImport_3748_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 1
                                                + 1)
                                                as u32,
                                        );
                                        crate::leanh::lean_dec_ref(v_toImport_3748_);
                                        if v_isExported_3749_ == 0 {
                                            v___y_3716_ = v___x_3676_;
                                            state = 32;
                                            continue;
                                        } else {
                                            v___y_3716_ = v___x_3496_;
                                            state = 32;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_3674_);
                                v___y_3664_ = v___x_3673_;
                                v___y_3665_ = v___y_3425_;
                                v___y_3666_ = v___y_3426_;
                                v___y_3667_ = v___y_3427_;
                                v___y_3668_ = v___y_3428_;
                                state = 27;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3437_);
                    crate::leanh::lean_dec(v_k_3430_);
                    v_init_3422_ = v___x_3439_;
                    v_x_3423_ = v_r_3432_;
                    v___y_3424_ = v_snd_3435_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_3446_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_3444_);
                if crate::leanh::lean_obj_tag(v___x_3446_) == 0 {
                    v_a_3447_ = crate::leanh::lean_ctor_get(v___x_3446_, 0);
                    crate::leanh::lean_inc(v_a_3447_);
                    crate::leanh::lean_dec_ref_known(v___x_3446_, 1);
                    v___x_3448_ = (crate::leanh::lean_unbox(v_a_3447_) as u8);
                    v___x_3449_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(
                        v_k_3430_,
                        v___x_3448_,
                        v___y_3442_,
                    );
                    crate::leanh::lean_dec(v_k_3430_);
                    if crate::leanh::lean_obj_tag(v___x_3449_) == 0 {
                        v_a_3450_ = crate::leanh::lean_ctor_get(v___x_3449_, 0);
                        crate::leanh::lean_inc(v_a_3450_);
                        crate::leanh::lean_dec_ref_known(v___x_3449_, 1);
                        if crate::leanh::lean_obj_tag(v_a_3450_) == 1 {
                            v_val_3451_ = crate::leanh::lean_ctor_get(v_a_3450_, 0);
                            crate::leanh::lean_inc(v_val_3451_);
                            crate::leanh::lean_dec_ref_known(v_a_3450_, 1);
                            v___x_3452_ = (crate::leanh::lean_unbox(v_a_3447_) as u8);
                            crate::leanh::lean_dec(v_a_3447_);
                            v___x_3453_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_3452_);
                            v___x_3454_ = l_Lean_Compiler_LCNF_Decl_castPurity_x21(
                                v___x_3453_,
                                v_val_3451_,
                                v_pu_3418_,
                            );
                            crate::leanh::lean_dec(v_val_3451_);
                            crate::leanh::lean_inc_ref(v_origDecl_3419_);
                            v___x_3455_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_3418_, v_origDecl_3419_, v_isMeta_3420_, v_isPublic_3421_, v___x_3454_, v___y_3443_, v___y_3444_, v___y_3441_, v___y_3445_, v___y_3442_);
                            if crate::leanh::lean_obj_tag(v___x_3455_) == 0 {
                                v_a_3456_ = crate::leanh::lean_ctor_get(v___x_3455_, 0);
                                crate::leanh::lean_inc(v_a_3456_);
                                crate::leanh::lean_dec_ref_known(v___x_3455_, 1);
                                v_snd_3457_ = crate::leanh::lean_ctor_get(v_a_3456_, 1);
                                crate::leanh::lean_inc(v_snd_3457_);
                                crate::leanh::lean_dec(v_a_3456_);
                                v_init_3422_ = v___x_3439_;
                                v_x_3423_ = v_r_3432_;
                                v___y_3424_ = v_snd_3457_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_r_3432_);
                                crate::leanh::lean_dec_ref(v_origDecl_3419_);
                                v_a_3459_ = crate::leanh::lean_ctor_get(v___x_3455_, 0);
                                v_isSharedCheck_3466_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3455_)) as u8;
                                if v_isSharedCheck_3466_ == 0 {
                                    v___x_3461_ = v___x_3455_;
                                    v_isShared_3462_ = v_isSharedCheck_3466_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3459_);
                                    crate::leanh::lean_dec(v___x_3455_);
                                    v___x_3461_ = crate::leanh::lean_box(0);
                                    v_isShared_3462_ = v_isSharedCheck_3466_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3450_);
                            crate::leanh::lean_dec(v_a_3447_);
                            v_init_3422_ = v___x_3439_;
                            v_x_3423_ = v_r_3432_;
                            v___y_3424_ = v___y_3443_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3447_);
                        crate::leanh::lean_dec(v___y_3443_);
                        crate::leanh::lean_dec(v_r_3432_);
                        crate::leanh::lean_dec_ref(v_origDecl_3419_);
                        v_a_3468_ = crate::leanh::lean_ctor_get(v___x_3449_, 0);
                        v_isSharedCheck_3475_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3449_)) as u8;
                        if v_isSharedCheck_3475_ == 0 {
                            v___x_3470_ = v___x_3449_;
                            v_isShared_3471_ = v_isSharedCheck_3475_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3468_);
                            crate::leanh::lean_dec(v___x_3449_);
                            v___x_3470_ = crate::leanh::lean_box(0);
                            v_isShared_3471_ = v_isSharedCheck_3475_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3443_);
                    crate::leanh::lean_dec(v_r_3432_);
                    crate::leanh::lean_dec(v_k_3430_);
                    crate::leanh::lean_dec_ref(v_origDecl_3419_);
                    v_a_3476_ = crate::leanh::lean_ctor_get(v___x_3446_, 0);
                    v_isSharedCheck_3483_ = (!crate::leanh::lean_is_exclusive(v___x_3446_)) as u8;
                    if v_isSharedCheck_3483_ == 0 {
                        v___x_3478_ = v___x_3446_;
                        v_isShared_3479_ = v_isSharedCheck_3483_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3476_);
                        crate::leanh::lean_dec(v___x_3446_);
                        v___x_3478_ = crate::leanh::lean_box(0);
                        v_isShared_3479_ = v_isSharedCheck_3483_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3462_ == 0 {
                    v___x_3464_ = v___x_3461_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
                    v___x_3464_ = v_reuseFailAlloc_3465_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3464_;
            }
            5 => {
                if v_isShared_3471_ == 0 {
                    v___x_3473_ = v___x_3470_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3474_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
                    v___x_3473_ = v_reuseFailAlloc_3474_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3473_;
            }
            7 => {
                if v_isShared_3479_ == 0 {
                    v___x_3481_ = v___x_3478_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3482_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
                    v___x_3481_ = v_reuseFailAlloc_3482_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3481_;
            }
            9 => {
                v___x_3491_ = 2;
                v___x_3492_ = l_Lean_instBEqIRPhases_beq(v___y_3485_, v___x_3491_);
                if v___x_3492_ == 0 {
                    if v_isPublic_3421_ == 0 {
                        crate::leanh::lean_dec(v_k_3430_);
                        v_init_3422_ = v___x_3439_;
                        v_x_3423_ = v_r_3432_;
                        v___y_3424_ = v___y_3486_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3494_ = l_Lean_isPrivateName(v_k_3430_);
                        if v___x_3494_ == 0 {
                            crate::leanh::lean_dec(v_k_3430_);
                            v_init_3422_ = v___x_3439_;
                            v_x_3423_ = v_r_3432_;
                            v___y_3424_ = v___y_3486_;
                            state = 0;
                            continue;
                        } else {
                            v___y_3441_ = v___y_3488_;
                            v___y_3442_ = v___y_3490_;
                            v___y_3443_ = v___y_3486_;
                            v___y_3444_ = v___y_3487_;
                            v___y_3445_ = v___y_3489_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___y_3441_ = v___y_3488_;
                    v___y_3442_ = v___y_3490_;
                    v___y_3443_ = v___y_3486_;
                    v___y_3444_ = v___y_3487_;
                    v___y_3445_ = v___y_3489_;
                    state = 2;
                    continue;
                }
            }
            10 => {
                v_toSignature_3503_ = crate::leanh::lean_ctor_get(v_origDecl_3419_, 0);
                crate::leanh::lean_inc_ref(v_toSignature_3503_);
                crate::leanh::lean_dec_ref(v_origDecl_3419_);
                v_name_3504_ = crate::leanh::lean_ctor_get(v_toSignature_3503_, 0);
                crate::leanh::lean_inc(v_name_3504_);
                crate::leanh::lean_dec_ref(v_toSignature_3503_);
                v___x_3505_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
                v___x_3506_ = l_Lean_MessageData_ofConstName(v_name_3504_, v___x_3496_);
                if v_isShared_3438_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3437_, 7);
                    crate::leanh::lean_ctor_set(v___x_3437_, 1, v___x_3506_);
                    crate::leanh::lean_ctor_set(v___x_3437_, 0, v___x_3505_);
                    v___x_3508_ = v___x_3437_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 1, v___x_3506_);
                    v___x_3508_ = v_reuseFailAlloc_3524_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3509_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
                v___x_3510_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3510_, 0, v___x_3508_);
                crate::leanh::lean_ctor_set(v___x_3510_, 1, v___x_3509_);
                v___x_3511_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3496_);
                v___x_3512_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3512_, 0, v___x_3510_);
                crate::leanh::lean_ctor_set(v___x_3512_, 1, v___x_3511_);
                v___x_3513_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5);
                v___x_3514_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3514_, 0, v___x_3512_);
                crate::leanh::lean_ctor_set(v___x_3514_, 1, v___x_3513_);
                v___x_3515_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3514_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
                v_a_3516_ = crate::leanh::lean_ctor_get(v___x_3515_, 0);
                v_isSharedCheck_3523_ = (!crate::leanh::lean_is_exclusive(v___x_3515_)) as u8;
                if v_isSharedCheck_3523_ == 0 {
                    v___x_3518_ = v___x_3515_;
                    v_isShared_3519_ = v_isSharedCheck_3523_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3516_);
                    crate::leanh::lean_dec(v___x_3515_);
                    v___x_3518_ = crate::leanh::lean_box(0);
                    v_isShared_3519_ = v_isSharedCheck_3523_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3519_ == 0 {
                    v___x_3521_ = v___x_3518_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3522_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
                    v___x_3521_ = v_reuseFailAlloc_3522_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3521_;
            }
            14 => {
                v_toSignature_3534_ = crate::leanh::lean_ctor_get(v_origDecl_3419_, 0);
                crate::leanh::lean_inc_ref(v_toSignature_3534_);
                crate::leanh::lean_dec_ref(v_origDecl_3419_);
                v_name_3535_ = crate::leanh::lean_ctor_get(v_toSignature_3534_, 0);
                crate::leanh::lean_inc(v_name_3535_);
                crate::leanh::lean_dec_ref(v_toSignature_3534_);
                v___x_3536_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
                v___x_3537_ = l_Lean_MessageData_ofConstName(v_name_3535_, v___x_3496_);
                v___x_3538_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3538_, 0, v___x_3536_);
                crate::leanh::lean_ctor_set(v___x_3538_, 1, v___x_3537_);
                v___x_3539_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
                v___x_3540_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3540_, 0, v___x_3538_);
                crate::leanh::lean_ctor_set(v___x_3540_, 1, v___x_3539_);
                v___x_3541_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3496_);
                v___x_3542_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3542_, 0, v___x_3540_);
                crate::leanh::lean_ctor_set(v___x_3542_, 1, v___x_3541_);
                v___x_3543_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7);
                v___x_3544_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3544_, 0, v___x_3542_);
                crate::leanh::lean_ctor_set(v___x_3544_, 1, v___x_3543_);
                v___x_3545_ = crate::leanh::lean_box(0);
                v___x_3546_ = l_Lean_Environment_header(v_env_3526_);
                crate::leanh::lean_dec_ref(v_env_3526_);
                v___x_3547_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3546_);
                v___x_3548_ = lean_array_get(v___x_3545_, v___x_3547_, v___y_3528_);
                crate::leanh::lean_dec(v___y_3528_);
                crate::leanh::lean_dec_ref(v___x_3547_);
                v___x_3549_ = l_Lean_MessageData_ofName(v___x_3548_);
                v___x_3550_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3550_, 0, v___x_3544_);
                crate::leanh::lean_ctor_set(v___x_3550_, 1, v___x_3549_);
                v___x_3551_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
                v___x_3552_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3552_, 0, v___x_3550_);
                crate::leanh::lean_ctor_set(v___x_3552_, 1, v___x_3551_);
                v___x_3553_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3552_, v___y_3531_, v___y_3530_, v___y_3529_, v___y_3532_);
                v_a_3554_ = crate::leanh::lean_ctor_get(v___x_3553_, 0);
                v_isSharedCheck_3561_ = (!crate::leanh::lean_is_exclusive(v___x_3553_)) as u8;
                if v_isSharedCheck_3561_ == 0 {
                    v___x_3556_ = v___x_3553_;
                    v_isShared_3557_ = v_isSharedCheck_3561_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3554_);
                    crate::leanh::lean_dec(v___x_3553_);
                    v___x_3556_ = crate::leanh::lean_box(0);
                    v_isShared_3557_ = v_isSharedCheck_3561_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3557_ == 0 {
                    v___x_3559_ = v___x_3556_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3560_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
                    v___x_3559_ = v_reuseFailAlloc_3560_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3559_;
            }
            17 => {
                v___x_3568_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3526_, v_k_3430_);
                if crate::leanh::lean_obj_tag(v___x_3568_) == 1 {
                    v_val_3569_ = crate::leanh::lean_ctor_get(v___x_3568_, 0);
                    crate::leanh::lean_inc(v_val_3569_);
                    crate::leanh::lean_dec_ref_known(v___x_3568_, 1);
                    crate::leanh::lean_inc(v_k_3430_);
                    crate::leanh::lean_inc_ref(v_env_3526_);
                    v___x_3570_ = l_Lean_isMarkedMeta(v_env_3526_, v_k_3430_);
                    if v___x_3570_ == 0 {
                        crate::leanh::lean_del_object(v___x_3437_);
                        v___y_3528_ = v_val_3569_;
                        v___y_3529_ = v___y_3564_;
                        v___y_3530_ = v___y_3563_;
                        v___y_3531_ = v___y_3565_;
                        v___y_3532_ = v___y_3566_;
                        v___y_3533_ = v___y_3567_;
                        state = 14;
                        continue;
                    } else {
                        if v___x_3496_ == 0 {
                            crate::leanh::lean_dec(v_val_3569_);
                            crate::leanh::lean_dec_ref(v_env_3526_);
                            v___y_3498_ = v___y_3567_;
                            v___y_3499_ = v___y_3565_;
                            v___y_3500_ = v___y_3563_;
                            v___y_3501_ = v___y_3564_;
                            v___y_3502_ = v___y_3566_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_3437_);
                            v___y_3528_ = v_val_3569_;
                            v___y_3529_ = v___y_3564_;
                            v___y_3530_ = v___y_3563_;
                            v___y_3531_ = v___y_3565_;
                            v___y_3532_ = v___y_3566_;
                            v___y_3533_ = v___y_3567_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3568_);
                    crate::leanh::lean_dec_ref(v_env_3526_);
                    v___y_3498_ = v___y_3567_;
                    v___y_3499_ = v___y_3565_;
                    v___y_3500_ = v___y_3563_;
                    v___y_3501_ = v___y_3564_;
                    v___y_3502_ = v___y_3566_;
                    state = 10;
                    continue;
                }
            }
            18 => {
                v___x_3578_ = 1;
                v___x_3579_ = l_Lean_instBEqIRPhases_beq(v___y_3577_, v___x_3578_);
                if v___x_3579_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_3526_);
                    crate::leanh::lean_del_object(v___x_3437_);
                    v___y_3485_ = v___y_3577_;
                    v___y_3486_ = v___y_3572_;
                    v___y_3487_ = v___y_3575_;
                    v___y_3488_ = v___y_3574_;
                    v___y_3489_ = v___y_3573_;
                    v___y_3490_ = v___y_3576_;
                    state = 9;
                    continue;
                } else {
                    if v_isMeta_3420_ == 0 {
                        crate::leanh::lean_dec(v___y_3572_);
                        crate::leanh::lean_dec(v_r_3432_);
                        v___y_3563_ = v___y_3574_;
                        v___y_3564_ = v___y_3573_;
                        v___y_3565_ = v___y_3575_;
                        v___y_3566_ = v___y_3576_;
                        v___y_3567_ = v___y_3577_;
                        state = 17;
                        continue;
                    } else {
                        if v___x_3496_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_3526_);
                            crate::leanh::lean_del_object(v___x_3437_);
                            v___y_3485_ = v___y_3577_;
                            v___y_3486_ = v___y_3572_;
                            v___y_3487_ = v___y_3575_;
                            v___y_3488_ = v___y_3574_;
                            v___y_3489_ = v___y_3573_;
                            v___y_3490_ = v___y_3576_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_3572_);
                            crate::leanh::lean_dec(v_r_3432_);
                            v___y_3563_ = v___y_3574_;
                            v___y_3564_ = v___y_3573_;
                            v___y_3565_ = v___y_3575_;
                            v___y_3566_ = v___y_3576_;
                            v___y_3567_ = v___y_3577_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v___x_3496_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_3526_);
                    crate::leanh::lean_del_object(v___x_3437_);
                    v___y_3485_ = v___y_3581_;
                    v___y_3486_ = v___y_3582_;
                    v___y_3487_ = v___y_3583_;
                    v___y_3488_ = v___y_3584_;
                    v___y_3489_ = v___y_3585_;
                    v___y_3490_ = v___y_3586_;
                    state = 9;
                    continue;
                } else {
                    v___y_3572_ = v___y_3582_;
                    v___y_3573_ = v___y_3585_;
                    v___y_3574_ = v___y_3584_;
                    v___y_3575_ = v___y_3583_;
                    v___y_3576_ = v___y_3586_;
                    v___y_3577_ = v___y_3581_;
                    state = 18;
                    continue;
                }
            }
            20 => {
                if v___y_3588_ == 0 {
                    v___y_3572_ = v___y_3590_;
                    v___y_3573_ = v___y_3593_;
                    v___y_3574_ = v___y_3592_;
                    v___y_3575_ = v___y_3591_;
                    v___y_3576_ = v___y_3594_;
                    v___y_3577_ = v___y_3589_;
                    state = 18;
                    continue;
                } else {
                    v___y_3581_ = v___y_3589_;
                    v___y_3582_ = v___y_3590_;
                    v___y_3583_ = v___y_3591_;
                    v___y_3584_ = v___y_3592_;
                    v___y_3585_ = v___y_3593_;
                    v___y_3586_ = v___y_3594_;
                    state = 19;
                    continue;
                }
            }
            21 => {
                v___x_3603_ = 0;
                v___x_3604_ = l_Lean_instBEqIRPhases_beq(v___y_3602_, v___x_3603_);
                if v___x_3604_ == 0 {
                    v___y_3588_ = v___y_3596_;
                    v___y_3589_ = v___y_3602_;
                    v___y_3590_ = v___y_3597_;
                    v___y_3591_ = v___y_3601_;
                    v___y_3592_ = v___y_3598_;
                    v___y_3593_ = v___y_3599_;
                    v___y_3594_ = v___y_3600_;
                    state = 20;
                    continue;
                } else {
                    if v_isMeta_3420_ == 0 {
                        v___y_3588_ = v___y_3596_;
                        v___y_3589_ = v___y_3602_;
                        v___y_3590_ = v___y_3597_;
                        v___y_3591_ = v___y_3601_;
                        v___y_3592_ = v___y_3598_;
                        v___y_3593_ = v___y_3599_;
                        v___y_3594_ = v___y_3600_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_3597_);
                        crate::leanh::lean_del_object(v___x_3437_);
                        crate::leanh::lean_dec(v_r_3432_);
                        v___x_3605_ =
                            l_Lean_Environment_getModuleIdxFor_x3f(v_env_3526_, v_k_3430_);
                        if crate::leanh::lean_obj_tag(v___x_3605_) == 1 {
                            v_toSignature_3606_ = crate::leanh::lean_ctor_get(v_origDecl_3419_, 0);
                            crate::leanh::lean_inc_ref(v_toSignature_3606_);
                            crate::leanh::lean_dec_ref(v_origDecl_3419_);
                            v_val_3607_ = crate::leanh::lean_ctor_get(v___x_3605_, 0);
                            crate::leanh::lean_inc(v_val_3607_);
                            crate::leanh::lean_dec_ref_known(v___x_3605_, 1);
                            v_name_3608_ = crate::leanh::lean_ctor_get(v_toSignature_3606_, 0);
                            crate::leanh::lean_inc(v_name_3608_);
                            crate::leanh::lean_dec_ref(v_toSignature_3606_);
                            v___x_3609_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
                            v___x_3610_ = l_Lean_MessageData_ofConstName(v_name_3608_, v___x_3496_);
                            v___x_3611_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3611_, 0, v___x_3609_);
                            crate::leanh::lean_ctor_set(v___x_3611_, 1, v___x_3610_);
                            v___x_3612_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
                            v___x_3613_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3613_, 0, v___x_3611_);
                            crate::leanh::lean_ctor_set(v___x_3613_, 1, v___x_3612_);
                            v___x_3614_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3496_);
                            v___x_3615_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3615_, 0, v___x_3613_);
                            crate::leanh::lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                            v___x_3616_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
                            v___x_3617_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3617_, 0, v___x_3615_);
                            crate::leanh::lean_ctor_set(v___x_3617_, 1, v___x_3616_);
                            v___x_3618_ = crate::leanh::lean_box(0);
                            v___x_3619_ = l_Lean_Environment_header(v_env_3526_);
                            crate::leanh::lean_dec_ref(v_env_3526_);
                            v___x_3620_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3619_);
                            v___x_3621_ = lean_array_get(v___x_3618_, v___x_3620_, v_val_3607_);
                            crate::leanh::lean_dec(v_val_3607_);
                            crate::leanh::lean_dec_ref(v___x_3620_);
                            v___x_3622_ = l_Lean_MessageData_ofName(v___x_3621_);
                            v___x_3623_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3623_, 0, v___x_3617_);
                            crate::leanh::lean_ctor_set(v___x_3623_, 1, v___x_3622_);
                            v___x_3624_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
                            v___x_3625_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3625_, 0, v___x_3623_);
                            crate::leanh::lean_ctor_set(v___x_3625_, 1, v___x_3624_);
                            v___x_3626_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3625_, v___y_3601_, v___y_3598_, v___y_3599_, v___y_3600_);
                            v_a_3627_ = crate::leanh::lean_ctor_get(v___x_3626_, 0);
                            v_isSharedCheck_3634_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3626_)) as u8;
                            if v_isSharedCheck_3634_ == 0 {
                                v___x_3629_ = v___x_3626_;
                                v_isShared_3630_ = v_isSharedCheck_3634_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3627_);
                                crate::leanh::lean_dec(v___x_3626_);
                                v___x_3629_ = crate::leanh::lean_box(0);
                                v_isShared_3630_ = v_isSharedCheck_3634_;
                                state = 22;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3605_);
                            crate::leanh::lean_dec_ref(v_env_3526_);
                            v_toSignature_3635_ = crate::leanh::lean_ctor_get(v_origDecl_3419_, 0);
                            crate::leanh::lean_inc_ref(v_toSignature_3635_);
                            crate::leanh::lean_dec_ref(v_origDecl_3419_);
                            v_name_3636_ = crate::leanh::lean_ctor_get(v_toSignature_3635_, 0);
                            crate::leanh::lean_inc(v_name_3636_);
                            crate::leanh::lean_dec_ref(v_toSignature_3635_);
                            v___x_3637_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
                            v___x_3638_ = l_Lean_MessageData_ofConstName(v_name_3636_, v___x_3496_);
                            v___x_3639_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3639_, 0, v___x_3637_);
                            crate::leanh::lean_ctor_set(v___x_3639_, 1, v___x_3638_);
                            v___x_3640_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
                            v___x_3641_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3641_, 0, v___x_3639_);
                            crate::leanh::lean_ctor_set(v___x_3641_, 1, v___x_3640_);
                            v___x_3642_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3496_);
                            v___x_3643_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3643_, 0, v___x_3641_);
                            crate::leanh::lean_ctor_set(v___x_3643_, 1, v___x_3642_);
                            v___x_3644_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17);
                            v___x_3645_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3645_, 0, v___x_3643_);
                            crate::leanh::lean_ctor_set(v___x_3645_, 1, v___x_3644_);
                            v___x_3646_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3645_, v___y_3601_, v___y_3598_, v___y_3599_, v___y_3600_);
                            v_a_3647_ = crate::leanh::lean_ctor_get(v___x_3646_, 0);
                            v_isSharedCheck_3654_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3646_)) as u8;
                            if v_isSharedCheck_3654_ == 0 {
                                v___x_3649_ = v___x_3646_;
                                v_isShared_3650_ = v_isSharedCheck_3654_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3647_);
                                crate::leanh::lean_dec(v___x_3646_);
                                v___x_3649_ = crate::leanh::lean_box(0);
                                v_isShared_3650_ = v_isSharedCheck_3654_;
                                state = 24;
                                continue;
                            }
                        }
                    }
                }
            }
            22 => {
                if v_isShared_3630_ == 0 {
                    v___x_3632_ = v___x_3629_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
                    v___x_3632_ = v_reuseFailAlloc_3633_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3632_;
            }
            24 => {
                if v_isShared_3650_ == 0 {
                    v___x_3652_ = v___x_3649_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
                    v___x_3652_ = v_reuseFailAlloc_3653_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3652_;
            }
            26 => {
                crate::leanh::lean_inc(v_k_3430_);
                crate::leanh::lean_inc_ref(v_env_3526_);
                v___x_3662_ = l_Lean_getIRPhases(v_env_3526_, v_k_3430_);
                if v___y_3661_ == 0 {
                    v___y_3596_ = v___y_3661_;
                    v___y_3597_ = v___y_3656_;
                    v___y_3598_ = v___y_3657_;
                    v___y_3599_ = v___y_3658_;
                    v___y_3600_ = v___y_3660_;
                    v___y_3601_ = v___y_3659_;
                    v___y_3602_ = v___x_3662_;
                    state = 21;
                    continue;
                } else {
                    if v___x_3496_ == 0 {
                        v___y_3581_ = v___x_3662_;
                        v___y_3582_ = v___y_3656_;
                        v___y_3583_ = v___y_3659_;
                        v___y_3584_ = v___y_3657_;
                        v___y_3585_ = v___y_3658_;
                        v___y_3586_ = v___y_3660_;
                        state = 19;
                        continue;
                    } else {
                        v___y_3596_ = v___y_3661_;
                        v___y_3597_ = v___y_3656_;
                        v___y_3598_ = v___y_3657_;
                        v___y_3599_ = v___y_3658_;
                        v___y_3600_ = v___y_3660_;
                        v___y_3601_ = v___y_3659_;
                        v___y_3602_ = v___x_3662_;
                        state = 21;
                        continue;
                    }
                }
            }
            27 => {
                v_options_3669_ = crate::leanh::lean_ctor_get(v___y_3667_, 2);
                v___x_3670_ = l_Lean_Compiler_compiler_relaxedMetaCheck;
                v___x_3671_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_3669_, v___x_3670_);
                if v___x_3671_ == 0 {
                    v___y_3656_ = v___y_3664_;
                    v___y_3657_ = v___y_3666_;
                    v___y_3658_ = v___y_3667_;
                    v___y_3659_ = v___y_3665_;
                    v___y_3660_ = v___y_3668_;
                    v___y_3661_ = v___x_3671_;
                    state = 26;
                    continue;
                } else {
                    v___x_3672_ = l_Lean_Environment_isImportedConst(v_env_3526_, v_k_3430_);
                    if v___x_3672_ == 0 {
                        v___y_3656_ = v___y_3664_;
                        v___y_3657_ = v___y_3666_;
                        v___y_3658_ = v___y_3667_;
                        v___y_3659_ = v___y_3665_;
                        v___y_3660_ = v___y_3668_;
                        v___y_3661_ = v___x_3671_;
                        state = 26;
                        continue;
                    } else {
                        v___y_3656_ = v___y_3664_;
                        v___y_3657_ = v___y_3666_;
                        v___y_3658_ = v___y_3667_;
                        v___y_3659_ = v___y_3665_;
                        v___y_3660_ = v___y_3668_;
                        v___y_3661_ = v___x_3496_;
                        state = 26;
                        continue;
                    }
                }
            }
            28 => {
                v_toSignature_3679_ = crate::leanh::lean_ctor_get(v_origDecl_3419_, 0);
                crate::leanh::lean_inc_ref(v_toSignature_3679_);
                crate::leanh::lean_dec_ref(v_origDecl_3419_);
                v_name_3680_ = crate::leanh::lean_ctor_get(v_toSignature_3679_, 0);
                crate::leanh::lean_inc(v_name_3680_);
                crate::leanh::lean_dec_ref(v_toSignature_3679_);
                v___x_3681_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
                v___x_3682_ = l_Lean_MessageData_ofConstName(v_name_3680_, v___x_3676_);
                v___x_3683_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3683_, 0, v___x_3681_);
                crate::leanh::lean_ctor_set(v___x_3683_, 1, v___x_3682_);
                v___x_3684_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
                v___x_3685_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3685_, 0, v___x_3683_);
                crate::leanh::lean_ctor_set(v___x_3685_, 1, v___x_3684_);
                v___x_3686_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3676_);
                v___x_3687_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3687_, 0, v___x_3685_);
                crate::leanh::lean_ctor_set(v___x_3687_, 1, v___x_3686_);
                v___x_3688_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
                v___x_3689_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3689_, 0, v___x_3687_);
                crate::leanh::lean_ctor_set(v___x_3689_, 1, v___x_3688_);
                v___x_3690_ = crate::leanh::lean_box(0);
                v___x_3691_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3677_);
                v___x_3692_ = lean_array_get(v___x_3690_, v___x_3691_, v_val_3675_);
                crate::leanh::lean_dec(v_val_3675_);
                crate::leanh::lean_dec_ref(v___x_3691_);
                v___x_3693_ = l_Lean_MessageData_ofName(v___x_3692_);
                v___x_3694_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3694_, 0, v___x_3689_);
                crate::leanh::lean_ctor_set(v___x_3694_, 1, v___x_3693_);
                v___x_3695_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
                v___x_3696_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3696_, 0, v___x_3694_);
                crate::leanh::lean_ctor_set(v___x_3696_, 1, v___x_3695_);
                v___x_3697_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3696_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
                v_a_3698_ = crate::leanh::lean_ctor_get(v___x_3697_, 0);
                v_isSharedCheck_3705_ = (!crate::leanh::lean_is_exclusive(v___x_3697_)) as u8;
                if v_isSharedCheck_3705_ == 0 {
                    v___x_3700_ = v___x_3697_;
                    v_isShared_3701_ = v_isSharedCheck_3705_;
                    state = 29;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3698_);
                    crate::leanh::lean_dec(v___x_3697_);
                    v___x_3700_ = crate::leanh::lean_box(0);
                    v_isShared_3701_ = v_isSharedCheck_3705_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_3701_ == 0 {
                    v___x_3703_ = v___x_3700_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
                    v___x_3703_ = v_reuseFailAlloc_3704_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3703_;
            }
            31 => {
                if v___y_3707_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3677_);
                    crate::leanh::lean_dec(v_val_3675_);
                    v___y_3664_ = v___x_3673_;
                    v___y_3665_ = v___y_3425_;
                    v___y_3666_ = v___y_3426_;
                    v___y_3667_ = v___y_3427_;
                    v___y_3668_ = v___y_3428_;
                    state = 27;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3673_);
                    crate::leanh::lean_dec_ref(v_env_3526_);
                    crate::leanh::lean_del_object(v___x_3437_);
                    crate::leanh::lean_dec(v_r_3432_);
                    state = 28;
                    continue;
                }
            }
            32 => {
                if v___y_3716_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3714_);
                    crate::leanh::lean_dec(v_val_3675_);
                    v___y_3664_ = v___x_3673_;
                    v___y_3665_ = v___y_3425_;
                    v___y_3666_ = v___y_3426_;
                    v___y_3667_ = v___y_3427_;
                    v___y_3668_ = v___y_3428_;
                    state = 27;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3673_);
                    crate::leanh::lean_dec_ref(v_env_3526_);
                    crate::leanh::lean_del_object(v___x_3437_);
                    crate::leanh::lean_dec(v_r_3432_);
                    v_toSignature_3717_ = crate::leanh::lean_ctor_get(v_origDecl_3419_, 0);
                    crate::leanh::lean_inc_ref(v_toSignature_3717_);
                    crate::leanh::lean_dec_ref(v_origDecl_3419_);
                    v_name_3718_ = crate::leanh::lean_ctor_get(v_toSignature_3717_, 0);
                    crate::leanh::lean_inc(v_name_3718_);
                    crate::leanh::lean_dec_ref(v_toSignature_3717_);
                    v___x_3719_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
                    v___x_3720_ = l_Lean_MessageData_ofConstName(v_name_3718_, v___x_3496_);
                    v___x_3721_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3721_, 0, v___x_3719_);
                    crate::leanh::lean_ctor_set(v___x_3721_, 1, v___x_3720_);
                    v___x_3722_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
                    v___x_3723_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3723_, 0, v___x_3721_);
                    crate::leanh::lean_ctor_set(v___x_3723_, 1, v___x_3722_);
                    v___x_3724_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3496_);
                    v___x_3725_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3725_, 0, v___x_3723_);
                    crate::leanh::lean_ctor_set(v___x_3725_, 1, v___x_3724_);
                    v___x_3726_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21);
                    v___x_3727_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3727_, 0, v___x_3725_);
                    crate::leanh::lean_ctor_set(v___x_3727_, 1, v___x_3726_);
                    v___x_3728_ = crate::leanh::lean_box(0);
                    v___x_3729_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3714_);
                    v___x_3730_ = lean_array_get(v___x_3728_, v___x_3729_, v_val_3675_);
                    crate::leanh::lean_dec(v_val_3675_);
                    crate::leanh::lean_dec_ref(v___x_3729_);
                    v___x_3731_ = l_Lean_MessageData_ofName(v___x_3730_);
                    v___x_3732_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3732_, 0, v___x_3727_);
                    crate::leanh::lean_ctor_set(v___x_3732_, 1, v___x_3731_);
                    v___x_3733_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
                    v___x_3734_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3734_, 0, v___x_3732_);
                    crate::leanh::lean_ctor_set(v___x_3734_, 1, v___x_3733_);
                    v___x_3735_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3734_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
                    v_a_3736_ = crate::leanh::lean_ctor_get(v___x_3735_, 0);
                    v_isSharedCheck_3743_ = (!crate::leanh::lean_is_exclusive(v___x_3735_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3738_ = v___x_3735_;
                        v_isShared_3739_ = v_isSharedCheck_3743_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3736_);
                        crate::leanh::lean_dec(v___x_3735_);
                        v___x_3738_ = crate::leanh::lean_box(0);
                        v_isShared_3739_ = v_isSharedCheck_3743_;
                        state = 33;
                        continue;
                    }
                }
            }
            33 => {
                if v_isShared_3739_ == 0 {
                    v___x_3741_ = v___x_3738_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3742_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
                    v___x_3741_ = v_reuseFailAlloc_3742_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(
    mut v_pu_3756_: u8,
    mut v_origDecl_3757_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3758_: u8,
    mut v_isPublic_3759_: u8,
    mut v_code_3760_: *mut crate::leanh::LeanObject,
    mut v___y_3761_: *mut crate::leanh::LeanObject,
    mut v___y_3762_: *mut crate::leanh::LeanObject,
    mut v___y_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
    mut v___y_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v_snd_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3778_: u8 = 0;
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_unused_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut v_a_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3767_ = l_Lean_NameSet_empty;
                v___x_3768_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_3756_, v_code_3760_, v___x_3767_);
                v___x_3769_ = crate::leanh::lean_box(0);
                v___x_3770_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_3756_, v_origDecl_3757_, v_isMeta_3758_, v_isPublic_3759_, v___x_3769_, v___x_3768_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
                if crate::leanh::lean_obj_tag(v___x_3770_) == 0 {
                    v_a_3771_ = crate::leanh::lean_ctor_get(v___x_3770_, 0);
                    v_isSharedCheck_3787_ = (!crate::leanh::lean_is_exclusive(v___x_3770_)) as u8;
                    if v_isSharedCheck_3787_ == 0 {
                        v___x_3773_ = v___x_3770_;
                        v_isShared_3774_ = v_isSharedCheck_3787_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3771_);
                        crate::leanh::lean_dec(v___x_3770_);
                        v___x_3773_ = crate::leanh::lean_box(0);
                        v_isShared_3774_ = v_isSharedCheck_3787_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3788_ = crate::leanh::lean_ctor_get(v___x_3770_, 0);
                    v_isSharedCheck_3795_ = (!crate::leanh::lean_is_exclusive(v___x_3770_)) as u8;
                    if v_isSharedCheck_3795_ == 0 {
                        v___x_3790_ = v___x_3770_;
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3788_);
                        crate::leanh::lean_dec(v___x_3770_);
                        v___x_3790_ = crate::leanh::lean_box(0);
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3775_ = crate::leanh::lean_ctor_get(v_a_3771_, 1);
                v_isSharedCheck_3785_ = (!crate::leanh::lean_is_exclusive(v_a_3771_)) as u8;
                if v_isSharedCheck_3785_ == 0 {
                    v_unused_3786_ = crate::leanh::lean_ctor_get(v_a_3771_, 0);
                    crate::leanh::lean_dec(v_unused_3786_);
                    v___x_3777_ = v_a_3771_;
                    v_isShared_3778_ = v_isSharedCheck_3785_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3775_);
                    crate::leanh::lean_dec(v_a_3771_);
                    v___x_3777_ = crate::leanh::lean_box(0);
                    v_isShared_3778_ = v_isSharedCheck_3785_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3778_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3777_, 0, v___x_3769_);
                    v___x_3780_ = v___x_3777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3784_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_snd_3775_);
                    v___x_3780_ = v_reuseFailAlloc_3784_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3774_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3773_, 0, v___x_3780_);
                    v___x_3782_ = v___x_3773_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3780_);
                    v___x_3782_ = v_reuseFailAlloc_3783_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3782_;
            }
            5 => {
                if v_isShared_3791_ == 0 {
                    v___x_3793_ = v___x_3790_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3794_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
                    v___x_3793_ = v_reuseFailAlloc_3794_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed(
    mut v_pu_3796_: *mut crate::leanh::LeanObject,
    mut v_origDecl_3797_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3798_: *mut crate::leanh::LeanObject,
    mut v_isPublic_3799_: *mut crate::leanh::LeanObject,
    mut v_code_3800_: *mut crate::leanh::LeanObject,
    mut v___y_3801_: *mut crate::leanh::LeanObject,
    mut v___y_3802_: *mut crate::leanh::LeanObject,
    mut v___y_3803_: *mut crate::leanh::LeanObject,
    mut v___y_3804_: *mut crate::leanh::LeanObject,
    mut v___y_3805_: *mut crate::leanh::LeanObject,
    mut v___y_3806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3807_: u8 = 0;
    let mut v_isMeta_boxed_3808_: u8 = 0;
    let mut v_isPublic_boxed_3809_: u8 = 0;
    let mut v_res_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3807_ = (crate::leanh::lean_unbox(v_pu_3796_) as u8);
    v_isMeta_boxed_3808_ = (crate::leanh::lean_unbox(v_isMeta_3798_) as u8);
    v_isPublic_boxed_3809_ = (crate::leanh::lean_unbox(v_isPublic_3799_) as u8);
    v_res_3810_ =
        l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0(
            v_pu_boxed_3807_,
            v_origDecl_3797_,
            v_isMeta_boxed_3808_,
            v_isPublic_boxed_3809_,
            v_code_3800_,
            v___y_3801_,
            v___y_3802_,
            v___y_3803_,
            v___y_3804_,
            v___y_3805_,
        );
    crate::leanh::lean_dec(v___y_3805_);
    crate::leanh::lean_dec_ref(v___y_3804_);
    crate::leanh::lean_dec(v___y_3803_);
    crate::leanh::lean_dec_ref(v___y_3802_);
    return v_res_3810_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(
    mut v_pu_3811_: u8,
    mut v_origDecl_3812_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3813_: u8,
    mut v_isPublic_3814_: u8,
    mut v_decl_3815_: *mut crate::leanh::LeanObject,
    mut v_a_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
    mut v_a_3819_: *mut crate::leanh::LeanObject,
    mut v_a_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_value_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_value_3822_ = crate::leanh::lean_ctor_get(v_decl_3815_, 1);
    crate::leanh::lean_inc_ref(v_value_3822_);
    crate::leanh::lean_dec_ref(v_decl_3815_);
    v___x_3823_ = crate::leanh::lean_box((v_pu_3811_) as usize);
    v___x_3824_ = crate::leanh::lean_box((v_isMeta_3813_) as usize);
    v___x_3825_ = crate::leanh::lean_box((v_isPublic_3814_) as usize);
    v___f_3826_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
    crate::leanh::lean_closure_set(v___f_3826_, 0, v___x_3823_);
    crate::leanh::lean_closure_set(v___f_3826_, 1, v_origDecl_3812_);
    crate::leanh::lean_closure_set(v___f_3826_, 2, v___x_3824_);
    crate::leanh::lean_closure_set(v___f_3826_, 3, v___x_3825_);
    v___x_3827_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_3826_, v_value_3822_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
    return v___x_3827_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___boxed(
    mut v_pu_3828_: *mut crate::leanh::LeanObject,
    mut v_origDecl_3829_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3830_: *mut crate::leanh::LeanObject,
    mut v_isPublic_3831_: *mut crate::leanh::LeanObject,
    mut v_decl_3832_: *mut crate::leanh::LeanObject,
    mut v_a_3833_: *mut crate::leanh::LeanObject,
    mut v_a_3834_: *mut crate::leanh::LeanObject,
    mut v_a_3835_: *mut crate::leanh::LeanObject,
    mut v_a_3836_: *mut crate::leanh::LeanObject,
    mut v_a_3837_: *mut crate::leanh::LeanObject,
    mut v_a_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3839_: u8 = 0;
    let mut v_isMeta_boxed_3840_: u8 = 0;
    let mut v_isPublic_boxed_3841_: u8 = 0;
    let mut v_res_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3839_ = (crate::leanh::lean_unbox(v_pu_3828_) as u8);
    v_isMeta_boxed_3840_ = (crate::leanh::lean_unbox(v_isMeta_3830_) as u8);
    v_isPublic_boxed_3841_ = (crate::leanh::lean_unbox(v_isPublic_3831_) as u8);
    v_res_3842_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(
        v_pu_boxed_3839_,
        v_origDecl_3829_,
        v_isMeta_boxed_3840_,
        v_isPublic_boxed_3841_,
        v_decl_3832_,
        v_a_3833_,
        v_a_3834_,
        v_a_3835_,
        v_a_3836_,
        v_a_3837_,
    );
    crate::leanh::lean_dec(v_a_3837_);
    crate::leanh::lean_dec_ref(v_a_3836_);
    crate::leanh::lean_dec(v_a_3835_);
    crate::leanh::lean_dec_ref(v_a_3834_);
    return v_res_3842_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___boxed(
    mut v_pu_3843_: *mut crate::leanh::LeanObject,
    mut v_origDecl_3844_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3845_: *mut crate::leanh::LeanObject,
    mut v_isPublic_3846_: *mut crate::leanh::LeanObject,
    mut v_init_3847_: *mut crate::leanh::LeanObject,
    mut v_x_3848_: *mut crate::leanh::LeanObject,
    mut v___y_3849_: *mut crate::leanh::LeanObject,
    mut v___y_3850_: *mut crate::leanh::LeanObject,
    mut v___y_3851_: *mut crate::leanh::LeanObject,
    mut v___y_3852_: *mut crate::leanh::LeanObject,
    mut v___y_3853_: *mut crate::leanh::LeanObject,
    mut v___y_3854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3855_: u8 = 0;
    let mut v_isMeta_boxed_3856_: u8 = 0;
    let mut v_isPublic_boxed_3857_: u8 = 0;
    let mut v_res_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3855_ = (crate::leanh::lean_unbox(v_pu_3843_) as u8);
    v_isMeta_boxed_3856_ = (crate::leanh::lean_unbox(v_isMeta_3845_) as u8);
    v_isPublic_boxed_3857_ = (crate::leanh::lean_unbox(v_isPublic_3846_) as u8);
    v_res_3858_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_boxed_3855_, v_origDecl_3844_, v_isMeta_boxed_3856_, v_isPublic_boxed_3857_, v_init_3847_, v_x_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
    crate::leanh::lean_dec(v___y_3853_);
    crate::leanh::lean_dec_ref(v___y_3852_);
    crate::leanh::lean_dec(v___y_3851_);
    crate::leanh::lean_dec_ref(v___y_3850_);
    return v_res_3858_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(
    mut v_opt_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_3862_ = crate::leanh::lean_ctor_get(v___y_3860_, 2);
    v___x_3863_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_3862_, v_opt_3859_);
    v___x_3864_ = crate::leanh::lean_box((v___x_3863_) as usize);
    v___x_3865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3865_, 0, v___x_3864_);
    return v___x_3865_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg___boxed(
    mut v_opt_3866_: *mut crate::leanh::LeanObject,
    mut v___y_3867_: *mut crate::leanh::LeanObject,
    mut v___y_3868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3869_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(
        v_opt_3866_,
        v___y_3867_,
    );
    crate::leanh::lean_dec_ref(v___y_3867_);
    crate::leanh::lean_dec_ref(v_opt_3866_);
    return v_res_3869_;
}
pub unsafe fn l_Lean_Compiler_LCNF_checkMeta(
    mut v_pu_3870_: u8,
    mut v_origDecl_3871_: *mut crate::leanh::LeanObject,
    mut v_a_3872_: *mut crate::leanh::LeanObject,
    mut v_a_3873_: *mut crate::leanh::LeanObject,
    mut v_a_3874_: *mut crate::leanh::LeanObject,
    mut v_a_3875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3889_: u8 = 0;
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_3897_: u8 = 0;
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: u8 = 0;
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: u8 = 0;
    let mut v___y_3906_: u8 = 0;
    let mut v___x_3907_: u8 = 0;
    let mut v___x_3908_: u8 = 0;
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v_fst_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3919_: u8 = 0;
    let mut v_a_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3929_: u8 = 0;
    let mut v___x_3930_: u8 = 0;
    let mut v___x_3931_: u8 = 0;
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3877_ = lean_st_ref_get(v_a_3875_);
                v___x_3878_ = l_Lean_Compiler_compiler_inLeanIR;
                v___x_3879_ =
                    l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(
                        v___x_3878_,
                        v_a_3874_,
                    );
                v_a_3880_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                v_isSharedCheck_3937_ = (!crate::leanh::lean_is_exclusive(v___x_3879_)) as u8;
                if v_isSharedCheck_3937_ == 0 {
                    v___x_3882_ = v___x_3879_;
                    v_isShared_3883_ = v_isSharedCheck_3937_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3880_);
                    crate::leanh::lean_dec(v___x_3879_);
                    v___x_3882_ = crate::leanh::lean_box(0);
                    v_isShared_3883_ = v_isSharedCheck_3937_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3884_ = l_Lean_Compiler_compiler_checkMeta;
                v___x_3885_ =
                    l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(
                        v___x_3884_,
                        v_a_3874_,
                    );
                v_a_3886_ = crate::leanh::lean_ctor_get(v___x_3885_, 0);
                v_isSharedCheck_3936_ = (!crate::leanh::lean_is_exclusive(v___x_3885_)) as u8;
                if v_isSharedCheck_3936_ == 0 {
                    v___x_3888_ = v___x_3885_;
                    v_isShared_3889_ = v_isSharedCheck_3936_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3886_);
                    crate::leanh::lean_dec(v___x_3885_);
                    v___x_3888_ = crate::leanh::lean_box(0);
                    v_isShared_3889_ = v_isSharedCheck_3936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_env_3895_ = crate::leanh::lean_ctor_get(v___x_3877_, 0);
                crate::leanh::lean_inc_ref(v_env_3895_);
                crate::leanh::lean_dec(v___x_3877_);
                v___x_3896_ = l_Lean_Environment_header(v_env_3895_);
                crate::leanh::lean_dec_ref(v_env_3895_);
                v_isModule_3897_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3896_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
                );
                crate::leanh::lean_dec_ref(v___x_3896_);
                if v_isModule_3897_ == 0 {
                    crate::leanh::lean_dec(v_a_3886_);
                    crate::leanh::lean_del_object(v___x_3882_);
                    crate::leanh::lean_dec(v_a_3880_);
                    crate::leanh::lean_dec_ref(v_origDecl_3871_);
                    state = 3;
                    continue;
                } else {
                    v___x_3898_ = (crate::leanh::lean_unbox(v_a_3880_) as u8);
                    crate::leanh::lean_dec(v_a_3880_);
                    if v___x_3898_ == 0 {
                        v___x_3899_ = (crate::leanh::lean_unbox(v_a_3886_) as u8);
                        if v___x_3899_ == 0 {
                            crate::leanh::lean_dec(v_a_3886_);
                            crate::leanh::lean_del_object(v___x_3882_);
                            crate::leanh::lean_dec_ref(v_origDecl_3871_);
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_3888_);
                            v___x_3900_ = lean_st_ref_get(v_a_3875_);
                            v_toSignature_3901_ = crate::leanh::lean_ctor_get(v_origDecl_3871_, 0);
                            v_env_3902_ = crate::leanh::lean_ctor_get(v___x_3900_, 0);
                            crate::leanh::lean_inc_ref(v_env_3902_);
                            crate::leanh::lean_dec(v___x_3900_);
                            v_name_3903_ = crate::leanh::lean_ctor_get(v_toSignature_3901_, 0);
                            crate::leanh::lean_inc(v_name_3903_);
                            v___x_3904_ = l_Lean_getIRPhases(v_env_3902_, v_name_3903_);
                            v___x_3928_ = 2;
                            v___x_3929_ = l_Lean_instBEqIRPhases_beq(v___x_3904_, v___x_3928_);
                            if v___x_3929_ == 0 {
                                crate::leanh::lean_del_object(v___x_3882_);
                                v___x_3930_ = l_Lean_isPrivateName(v_name_3903_);
                                if v___x_3930_ == 0 {
                                    v___x_3931_ = (crate::leanh::lean_unbox(v_a_3886_) as u8);
                                    crate::leanh::lean_dec(v_a_3886_);
                                    v___y_3906_ = v___x_3931_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3886_);
                                    v___y_3906_ = v___x_3929_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3886_);
                                crate::leanh::lean_dec_ref(v_origDecl_3871_);
                                v___x_3932_ = crate::leanh::lean_box(0);
                                if v_isShared_3883_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3882_, 0, v___x_3932_);
                                    v___x_3934_ = v___x_3882_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3935_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3935_,
                                        0,
                                        v___x_3932_,
                                    );
                                    v___x_3934_ = v_reuseFailAlloc_3935_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3886_);
                        crate::leanh::lean_del_object(v___x_3882_);
                        crate::leanh::lean_dec_ref(v_origDecl_3871_);
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3891_ = crate::leanh::lean_box(0);
                if v_isShared_3889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3888_, 0, v___x_3891_);
                    v___x_3893_ = v___x_3888_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
                    v___x_3893_ = v_reuseFailAlloc_3894_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3893_;
            }
            5 => {
                v___x_3907_ = 1;
                v___x_3908_ = l_Lean_instBEqIRPhases_beq(v___x_3904_, v___x_3907_);
                v___x_3909_ = l_Lean_NameSet_empty;
                crate::leanh::lean_inc_ref(v_origDecl_3871_);
                v___x_3910_ =
                    l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(
                        v_pu_3870_,
                        v_origDecl_3871_,
                        v___x_3908_,
                        v___y_3906_,
                        v_origDecl_3871_,
                        v___x_3909_,
                        v_a_3872_,
                        v_a_3873_,
                        v_a_3874_,
                        v_a_3875_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3910_) == 0 {
                    v_a_3911_ = crate::leanh::lean_ctor_get(v___x_3910_, 0);
                    v_isSharedCheck_3919_ = (!crate::leanh::lean_is_exclusive(v___x_3910_)) as u8;
                    if v_isSharedCheck_3919_ == 0 {
                        v___x_3913_ = v___x_3910_;
                        v_isShared_3914_ = v_isSharedCheck_3919_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3911_);
                        crate::leanh::lean_dec(v___x_3910_);
                        v___x_3913_ = crate::leanh::lean_box(0);
                        v_isShared_3914_ = v_isSharedCheck_3919_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_3920_ = crate::leanh::lean_ctor_get(v___x_3910_, 0);
                    v_isSharedCheck_3927_ = (!crate::leanh::lean_is_exclusive(v___x_3910_)) as u8;
                    if v_isSharedCheck_3927_ == 0 {
                        v___x_3922_ = v___x_3910_;
                        v_isShared_3923_ = v_isSharedCheck_3927_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3920_);
                        crate::leanh::lean_dec(v___x_3910_);
                        v___x_3922_ = crate::leanh::lean_box(0);
                        v_isShared_3923_ = v_isSharedCheck_3927_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v_fst_3915_ = crate::leanh::lean_ctor_get(v_a_3911_, 0);
                crate::leanh::lean_inc(v_fst_3915_);
                crate::leanh::lean_dec(v_a_3911_);
                if v_isShared_3914_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3913_, 0, v_fst_3915_);
                    v___x_3917_ = v___x_3913_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3918_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_fst_3915_);
                    v___x_3917_ = v_reuseFailAlloc_3918_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3917_;
            }
            8 => {
                if v_isShared_3923_ == 0 {
                    v___x_3925_ = v___x_3922_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3926_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
                    v___x_3925_ = v_reuseFailAlloc_3926_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3925_;
            }
            10 => {
                return v___x_3934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_checkMeta___boxed(
    mut v_pu_3938_: *mut crate::leanh::LeanObject,
    mut v_origDecl_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
    mut v_a_3941_: *mut crate::leanh::LeanObject,
    mut v_a_3942_: *mut crate::leanh::LeanObject,
    mut v_a_3943_: *mut crate::leanh::LeanObject,
    mut v_a_3944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3945_: u8 = 0;
    let mut v_res_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3945_ = (crate::leanh::lean_unbox(v_pu_3938_) as u8);
    v_res_3946_ = l_Lean_Compiler_LCNF_checkMeta(
        v_pu_boxed_3945_,
        v_origDecl_3939_,
        v_a_3940_,
        v_a_3941_,
        v_a_3942_,
        v_a_3943_,
    );
    crate::leanh::lean_dec(v_a_3943_);
    crate::leanh::lean_dec_ref(v_a_3942_);
    crate::leanh::lean_dec(v_a_3941_);
    crate::leanh::lean_dec_ref(v_a_3940_);
    return v_res_3946_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(
    mut v_opt_3947_: *mut crate::leanh::LeanObject,
    mut v___y_3948_: *mut crate::leanh::LeanObject,
    mut v___y_3949_: *mut crate::leanh::LeanObject,
    mut v___y_3950_: *mut crate::leanh::LeanObject,
    mut v___y_3951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3953_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(
        v_opt_3947_,
        v___y_3950_,
    );
    return v___x_3953_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___boxed(
    mut v_opt_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
    mut v___y_3957_: *mut crate::leanh::LeanObject,
    mut v___y_3958_: *mut crate::leanh::LeanObject,
    mut v___y_3959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3960_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(
        v_opt_3954_,
        v___y_3955_,
        v___y_3956_,
        v___y_3957_,
        v___y_3958_,
    );
    crate::leanh::lean_dec(v___y_3958_);
    crate::leanh::lean_dec_ref(v___y_3957_);
    crate::leanh::lean_dec(v___y_3956_);
    crate::leanh::lean_dec_ref(v___y_3955_);
    crate::leanh::lean_dec_ref(v_opt_3954_);
    return v_res_3960_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(
    mut v_isExporting_3961_: u8,
    mut v___x_3962_: *mut crate::leanh::LeanObject,
    mut v_x_3963_: *mut crate::leanh::LeanObject,
    mut v___y_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
    mut v___y_3967_: *mut crate::leanh::LeanObject,
    mut v___y_3968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3981_: u8 = 0;
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3990_: u8 = 0;
    let mut v_unused_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3970_ = lean_st_ref_take(v___y_3968_);
                v_env_3971_ = crate::leanh::lean_ctor_get(v___x_3970_, 0);
                v_nextMacroScope_3972_ = crate::leanh::lean_ctor_get(v___x_3970_, 1);
                v_ngen_3973_ = crate::leanh::lean_ctor_get(v___x_3970_, 2);
                v_auxDeclNGen_3974_ = crate::leanh::lean_ctor_get(v___x_3970_, 3);
                v_traceState_3975_ = crate::leanh::lean_ctor_get(v___x_3970_, 4);
                v_messages_3976_ = crate::leanh::lean_ctor_get(v___x_3970_, 6);
                v_infoState_3977_ = crate::leanh::lean_ctor_get(v___x_3970_, 7);
                v_snapshotTasks_3978_ = crate::leanh::lean_ctor_get(v___x_3970_, 8);
                v_isSharedCheck_3990_ = (!crate::leanh::lean_is_exclusive(v___x_3970_)) as u8;
                if v_isSharedCheck_3990_ == 0 {
                    v_unused_3991_ = crate::leanh::lean_ctor_get(v___x_3970_, 5);
                    crate::leanh::lean_dec(v_unused_3991_);
                    v___x_3980_ = v___x_3970_;
                    v_isShared_3981_ = v_isSharedCheck_3990_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3978_);
                    crate::leanh::lean_inc(v_infoState_3977_);
                    crate::leanh::lean_inc(v_messages_3976_);
                    crate::leanh::lean_inc(v_traceState_3975_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3974_);
                    crate::leanh::lean_inc(v_ngen_3973_);
                    crate::leanh::lean_inc(v_nextMacroScope_3972_);
                    crate::leanh::lean_inc(v_env_3971_);
                    crate::leanh::lean_dec(v___x_3970_);
                    v___x_3980_ = crate::leanh::lean_box(0);
                    v_isShared_3981_ = v_isSharedCheck_3990_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3982_ = l_Lean_Environment_setExporting(v_env_3971_, v_isExporting_3961_);
                if v_isShared_3981_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3980_, 5, v___x_3962_);
                    crate::leanh::lean_ctor_set(v___x_3980_, 0, v___x_3982_);
                    v___x_3984_ = v___x_3980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3989_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3982_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 1, v_nextMacroScope_3972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 2, v_ngen_3973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 3, v_auxDeclNGen_3974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 4, v_traceState_3975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 5, v___x_3962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 6, v_messages_3976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 7, v_infoState_3977_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 8, v_snapshotTasks_3978_);
                    v___x_3984_ = v_reuseFailAlloc_3989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3985_ = lean_st_ref_set(v___y_3968_, v___x_3984_);
                v___x_3986_ = crate::leanh::lean_box(0);
                v___x_3987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3987_, 0, v___x_3986_);
                crate::leanh::lean_ctor_set(v___x_3987_, 1, v___y_3964_);
                v___x_3988_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3988_, 0, v___x_3987_);
                return v___x_3988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed(
    mut v_isExporting_3992_: *mut crate::leanh::LeanObject,
    mut v___x_3993_: *mut crate::leanh::LeanObject,
    mut v_x_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
    mut v___y_3996_: *mut crate::leanh::LeanObject,
    mut v___y_3997_: *mut crate::leanh::LeanObject,
    mut v___y_3998_: *mut crate::leanh::LeanObject,
    mut v___y_3999_: *mut crate::leanh::LeanObject,
    mut v___y_4000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4001_: u8 = 0;
    let mut v_res_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4001_ = (crate::leanh::lean_unbox(v_isExporting_3992_) as u8);
    v_res_4002_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(v_isExporting_boxed_4001_, v___x_3993_, v_x_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
    crate::leanh::lean_dec(v___y_3999_);
    crate::leanh::lean_dec_ref(v___y_3998_);
    crate::leanh::lean_dec(v___y_3997_);
    crate::leanh::lean_dec_ref(v___y_3996_);
    crate::leanh::lean_dec(v_x_3994_);
    return v_res_4002_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(
    mut v___f_4003_: *mut crate::leanh::LeanObject,
    mut v___y_4004_: *mut crate::leanh::LeanObject,
    mut v___y_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4016_: u8 = 0;
    let mut v_fst_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_x3f_4009_) == 0 {
                    v___x_4011_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___y_4008_);
                    crate::leanh::lean_inc_ref(v___y_4007_);
                    crate::leanh::lean_inc(v___y_4006_);
                    crate::leanh::lean_inc_ref(v___y_4005_);
                    v___x_4012_ = crate::leanh::lean_apply_7(
                        v___f_4003_,
                        v___x_4011_,
                        v___y_4004_,
                        v___y_4005_,
                        v___y_4006_,
                        v___y_4007_,
                        v___y_4008_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4012_;
                } else {
                    crate::leanh::lean_dec(v___y_4004_);
                    v_val_4013_ = crate::leanh::lean_ctor_get(v_a_x3f_4009_, 0);
                    v_isSharedCheck_4023_ = (!crate::leanh::lean_is_exclusive(v_a_x3f_4009_)) as u8;
                    if v_isSharedCheck_4023_ == 0 {
                        v___x_4015_ = v_a_x3f_4009_;
                        v_isShared_4016_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4013_);
                        crate::leanh::lean_dec(v_a_x3f_4009_);
                        v___x_4015_ = crate::leanh::lean_box(0);
                        v_isShared_4016_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4017_ = crate::leanh::lean_ctor_get(v_val_4013_, 0);
                crate::leanh::lean_inc(v_fst_4017_);
                v_snd_4018_ = crate::leanh::lean_ctor_get(v_val_4013_, 1);
                crate::leanh::lean_inc(v_snd_4018_);
                crate::leanh::lean_dec(v_val_4013_);
                if v_isShared_4016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4015_, 0, v_fst_4017_);
                    v___x_4020_ = v___x_4015_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_fst_4017_);
                    v___x_4020_ = v_reuseFailAlloc_4022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_4008_);
                crate::leanh::lean_inc_ref(v___y_4007_);
                crate::leanh::lean_inc(v___y_4006_);
                crate::leanh::lean_inc_ref(v___y_4005_);
                v___x_4021_ = crate::leanh::lean_apply_7(
                    v___f_4003_,
                    v___x_4020_,
                    v_snd_4018_,
                    v___y_4005_,
                    v___y_4006_,
                    v___y_4007_,
                    v___y_4008_,
                    crate::leanh::lean_box(0),
                );
                return v___x_4021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1___boxed(
    mut v___f_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
    mut v___y_4027_: *mut crate::leanh::LeanObject,
    mut v___y_4028_: *mut crate::leanh::LeanObject,
    mut v___y_4029_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4030_: *mut crate::leanh::LeanObject,
    mut v___y_4031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4032_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v_a_x3f_4030_);
    crate::leanh::lean_dec(v___y_4029_);
    crate::leanh::lean_dec_ref(v___y_4028_);
    crate::leanh::lean_dec(v___y_4027_);
    crate::leanh::lean_dec_ref(v___y_4026_);
    return v_res_4032_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(
    mut v_x_4033_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4034_: u8,
    mut v___y_4035_: *mut crate::leanh::LeanObject,
    mut v___y_4036_: *mut crate::leanh::LeanObject,
    mut v___y_4037_: *mut crate::leanh::LeanObject,
    mut v___y_4038_: *mut crate::leanh::LeanObject,
    mut v___y_4039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4043_: u8 = 0;
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4067_: u8 = 0;
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4074_: u8 = 0;
    let mut v_fst_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v_unused_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4088_: u8 = 0;
    let mut v_a_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4096_: u8 = 0;
    let mut v_reuseFailAlloc_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_a_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4108_: u8 = 0;
    let mut v_unused_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4113_: u8 = 0;
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut v_reuseFailAlloc_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4119_: u8 = 0;
    let mut v_unused_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4041_ = lean_st_ref_get(v___y_4039_);
                v_env_4042_ = crate::leanh::lean_ctor_get(v___x_4041_, 0);
                crate::leanh::lean_inc_ref(v_env_4042_);
                crate::leanh::lean_dec(v___x_4041_);
                v_isExporting_4043_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_4042_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_4042_);
                v___x_4044_ = lean_st_ref_take(v___y_4039_);
                v_env_4045_ = crate::leanh::lean_ctor_get(v___x_4044_, 0);
                v_nextMacroScope_4046_ = crate::leanh::lean_ctor_get(v___x_4044_, 1);
                v_ngen_4047_ = crate::leanh::lean_ctor_get(v___x_4044_, 2);
                v_auxDeclNGen_4048_ = crate::leanh::lean_ctor_get(v___x_4044_, 3);
                v_traceState_4049_ = crate::leanh::lean_ctor_get(v___x_4044_, 4);
                v_messages_4050_ = crate::leanh::lean_ctor_get(v___x_4044_, 6);
                v_infoState_4051_ = crate::leanh::lean_ctor_get(v___x_4044_, 7);
                v_snapshotTasks_4052_ = crate::leanh::lean_ctor_get(v___x_4044_, 8);
                v_isSharedCheck_4119_ = (!crate::leanh::lean_is_exclusive(v___x_4044_)) as u8;
                if v_isSharedCheck_4119_ == 0 {
                    v_unused_4120_ = crate::leanh::lean_ctor_get(v___x_4044_, 5);
                    crate::leanh::lean_dec(v_unused_4120_);
                    v___x_4054_ = v___x_4044_;
                    v_isShared_4055_ = v_isSharedCheck_4119_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4052_);
                    crate::leanh::lean_inc(v_infoState_4051_);
                    crate::leanh::lean_inc(v_messages_4050_);
                    crate::leanh::lean_inc(v_traceState_4049_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4048_);
                    crate::leanh::lean_inc(v_ngen_4047_);
                    crate::leanh::lean_inc(v_nextMacroScope_4046_);
                    crate::leanh::lean_inc(v_env_4045_);
                    crate::leanh::lean_dec(v___x_4044_);
                    v___x_4054_ = crate::leanh::lean_box(0);
                    v_isShared_4055_ = v_isSharedCheck_4119_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4056_ = l_Lean_Environment_setExporting(v_env_4045_, v_isExporting_4034_);
                v___x_4057_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2,
                );
                if v_isShared_4055_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4054_, 5, v___x_4057_);
                    crate::leanh::lean_ctor_set(v___x_4054_, 0, v___x_4056_);
                    v___x_4059_ = v___x_4054_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4118_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_nextMacroScope_4046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 2, v_ngen_4047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 3, v_auxDeclNGen_4048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 4, v_traceState_4049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 5, v___x_4057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 6, v_messages_4050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 7, v_infoState_4051_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 8, v_snapshotTasks_4052_);
                    v___x_4059_ = v_reuseFailAlloc_4118_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4060_ = lean_st_ref_set(v___y_4039_, v___x_4059_);
                v___x_4061_ = crate::leanh::lean_box((v_isExporting_4043_) as usize);
                v___f_4062_ = crate::leanh::lean_alloc_closure(l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                crate::leanh::lean_closure_set(v___f_4062_, 0, v___x_4061_);
                crate::leanh::lean_closure_set(v___f_4062_, 1, v___x_4057_);
                crate::leanh::lean_inc(v___y_4039_);
                crate::leanh::lean_inc_ref(v___y_4038_);
                crate::leanh::lean_inc(v___y_4037_);
                crate::leanh::lean_inc_ref(v___y_4036_);
                crate::leanh::lean_inc(v___y_4035_);
                v_r_4063_ = crate::leanh::lean_apply_6(
                    v_x_4033_,
                    v___y_4035_,
                    v___y_4036_,
                    v___y_4037_,
                    v___y_4038_,
                    v___y_4039_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_4063_) == 0 {
                    v_a_4064_ = crate::leanh::lean_ctor_get(v_r_4063_, 0);
                    v_isSharedCheck_4098_ = (!crate::leanh::lean_is_exclusive(v_r_4063_)) as u8;
                    if v_isSharedCheck_4098_ == 0 {
                        v___x_4066_ = v_r_4063_;
                        v_isShared_4067_ = v_isSharedCheck_4098_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4064_);
                        crate::leanh::lean_dec(v_r_4063_);
                        v___x_4066_ = crate::leanh::lean_box(0);
                        v_isShared_4067_ = v_isSharedCheck_4098_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4099_ = crate::leanh::lean_ctor_get(v_r_4063_, 0);
                    crate::leanh::lean_inc(v_a_4099_);
                    crate::leanh::lean_dec_ref_known(v_r_4063_, 1);
                    v___x_4100_ = crate::leanh::lean_box(0);
                    v___x_4101_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_4062_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___x_4100_);
                    if crate::leanh::lean_obj_tag(v___x_4101_) == 0 {
                        v_isSharedCheck_4108_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4101_)) as u8;
                        if v_isSharedCheck_4108_ == 0 {
                            v_unused_4109_ = crate::leanh::lean_ctor_get(v___x_4101_, 0);
                            crate::leanh::lean_dec(v_unused_4109_);
                            v___x_4103_ = v___x_4101_;
                            v_isShared_4104_ = v_isSharedCheck_4108_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4101_);
                            v___x_4103_ = crate::leanh::lean_box(0);
                            v_isShared_4104_ = v_isSharedCheck_4108_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4099_);
                        v_a_4110_ = crate::leanh::lean_ctor_get(v___x_4101_, 0);
                        v_isSharedCheck_4117_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4101_)) as u8;
                        if v_isSharedCheck_4117_ == 0 {
                            v___x_4112_ = v___x_4101_;
                            v_isShared_4113_ = v_isSharedCheck_4117_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4110_);
                            crate::leanh::lean_dec(v___x_4101_);
                            v___x_4112_ = crate::leanh::lean_box(0);
                            v_isShared_4113_ = v_isSharedCheck_4117_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_4064_);
                if v_isShared_4067_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4066_, 1);
                    v___x_4069_ = v___x_4066_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4064_);
                    v___x_4069_ = v_reuseFailAlloc_4097_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4070_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_4062_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___x_4069_);
                if crate::leanh::lean_obj_tag(v___x_4070_) == 0 {
                    v_a_4071_ = crate::leanh::lean_ctor_get(v___x_4070_, 0);
                    v_isSharedCheck_4088_ = (!crate::leanh::lean_is_exclusive(v___x_4070_)) as u8;
                    if v_isSharedCheck_4088_ == 0 {
                        v___x_4073_ = v___x_4070_;
                        v_isShared_4074_ = v_isSharedCheck_4088_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4071_);
                        crate::leanh::lean_dec(v___x_4070_);
                        v___x_4073_ = crate::leanh::lean_box(0);
                        v_isShared_4074_ = v_isSharedCheck_4088_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4064_);
                    v_a_4089_ = crate::leanh::lean_ctor_get(v___x_4070_, 0);
                    v_isSharedCheck_4096_ = (!crate::leanh::lean_is_exclusive(v___x_4070_)) as u8;
                    if v_isSharedCheck_4096_ == 0 {
                        v___x_4091_ = v___x_4070_;
                        v_isShared_4092_ = v_isSharedCheck_4096_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4089_);
                        crate::leanh::lean_dec(v___x_4070_);
                        v___x_4091_ = crate::leanh::lean_box(0);
                        v_isShared_4092_ = v_isSharedCheck_4096_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v_fst_4075_ = crate::leanh::lean_ctor_get(v_a_4064_, 0);
                crate::leanh::lean_inc(v_fst_4075_);
                crate::leanh::lean_dec(v_a_4064_);
                v_snd_4076_ = crate::leanh::lean_ctor_get(v_a_4071_, 1);
                v_isSharedCheck_4086_ = (!crate::leanh::lean_is_exclusive(v_a_4071_)) as u8;
                if v_isSharedCheck_4086_ == 0 {
                    v_unused_4087_ = crate::leanh::lean_ctor_get(v_a_4071_, 0);
                    crate::leanh::lean_dec(v_unused_4087_);
                    v___x_4078_ = v_a_4071_;
                    v_isShared_4079_ = v_isSharedCheck_4086_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4076_);
                    crate::leanh::lean_dec(v_a_4071_);
                    v___x_4078_ = crate::leanh::lean_box(0);
                    v_isShared_4079_ = v_isSharedCheck_4086_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4079_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4078_, 0, v_fst_4075_);
                    v___x_4081_ = v___x_4078_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4085_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_fst_4075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_snd_4076_);
                    v___x_4081_ = v_reuseFailAlloc_4085_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4074_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4073_, 0, v___x_4081_);
                    v___x_4083_ = v___x_4073_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4081_);
                    v___x_4083_ = v_reuseFailAlloc_4084_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4083_;
            }
            9 => {
                if v_isShared_4092_ == 0 {
                    v___x_4094_ = v___x_4091_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
                    v___x_4094_ = v_reuseFailAlloc_4095_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4094_;
            }
            11 => {
                if v_isShared_4104_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4103_, 1);
                    crate::leanh::lean_ctor_set(v___x_4103_, 0, v_a_4099_);
                    v___x_4106_ = v___x_4103_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4107_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4099_);
                    v___x_4106_ = v_reuseFailAlloc_4107_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4106_;
            }
            13 => {
                if v_isShared_4113_ == 0 {
                    v___x_4115_ = v___x_4112_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
                    v___x_4115_ = v_reuseFailAlloc_4116_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___boxed(
    mut v_x_4121_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4129_: u8 = 0;
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4129_ = (crate::leanh::lean_unbox(v_isExporting_4122_) as u8);
    v_res_4130_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_4121_, v_isExporting_boxed_4129_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
    crate::leanh::lean_dec(v___y_4127_);
    crate::leanh::lean_dec_ref(v___y_4126_);
    crate::leanh::lean_dec(v___y_4125_);
    crate::leanh::lean_dec_ref(v___y_4124_);
    return v_res_4130_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(
    mut v_00_u03b1_4131_: *mut crate::leanh::LeanObject,
    mut v_x_4132_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4133_: u8,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_4132_, v_isExporting_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
    return v___x_4140_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(
    mut v_00_u03b1_4141_: *mut crate::leanh::LeanObject,
    mut v_x_4142_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4150_: u8 = 0;
    let mut v_res_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4150_ = (crate::leanh::lean_unbox(v_isExporting_4143_) as u8);
    v_res_4151_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(v_00_u03b1_4141_, v_x_4142_, v_isExporting_boxed_4150_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
    crate::leanh::lean_dec(v___y_4148_);
    crate::leanh::lean_dec_ref(v___y_4147_);
    crate::leanh::lean_dec(v___y_4146_);
    crate::leanh::lean_dec_ref(v___y_4145_);
    return v_res_4151_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(
    mut v_opt_4152_: *mut crate::leanh::LeanObject,
    mut v___y_4153_: *mut crate::leanh::LeanObject,
    mut v___y_4154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_4156_ = crate::leanh::lean_ctor_get(v___y_4154_, 2);
    v___x_4157_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_4156_, v_opt_4152_);
    v___x_4158_ = crate::leanh::lean_box((v___x_4157_) as usize);
    v___x_4159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4159_, 0, v___x_4158_);
    crate::leanh::lean_ctor_set(v___x_4159_, 1, v___y_4153_);
    v___x_4160_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4160_, 0, v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg___boxed(
    mut v_opt_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4165_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_4161_, v___y_4162_, v___y_4163_);
    crate::leanh::lean_dec_ref(v___y_4163_);
    crate::leanh::lean_dec_ref(v_opt_4161_);
    return v_res_4165_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(
    mut v_cls_4166_: *mut crate::leanh::LeanObject,
    mut v_msg_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4182_: u8 = 0;
    let mut v_env_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4201_: u8 = 0;
    let mut v_tid_4202_: u64 = 0;
    let mut v_traces_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4207_: u8 = 0;
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: f64 = 0.0;
    let mut v___x_4214_: u8 = 0;
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4234_: u8 = 0;
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut v_isSharedCheck_4236_: u8 = 0;
    let mut v_unused_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v_a_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4242_: u8 = 0;
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4174_ = crate::leanh::lean_ctor_get(v___y_4171_, 2);
                v_ref_4175_ = crate::leanh::lean_ctor_get(v___y_4171_, 5);
                v___x_4176_ = lean_st_ref_get(v___y_4172_);
                v___x_4177_ = lean_st_ref_get(v___y_4170_);
                v___x_4178_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4169_);
                if crate::leanh::lean_obj_tag(v___x_4178_) == 0 {
                    v_a_4179_ = crate::leanh::lean_ctor_get(v___x_4178_, 0);
                    v_isSharedCheck_4238_ = (!crate::leanh::lean_is_exclusive(v___x_4178_)) as u8;
                    if v_isSharedCheck_4238_ == 0 {
                        v___x_4181_ = v___x_4178_;
                        v_isShared_4182_ = v_isSharedCheck_4238_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4179_);
                        crate::leanh::lean_dec(v___x_4178_);
                        v___x_4181_ = crate::leanh::lean_box(0);
                        v_isShared_4182_ = v_isSharedCheck_4238_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4177_);
                    crate::leanh::lean_dec(v___x_4176_);
                    crate::leanh::lean_dec(v___y_4168_);
                    crate::leanh::lean_dec_ref(v_msg_4167_);
                    crate::leanh::lean_dec(v_cls_4166_);
                    v_a_4239_ = crate::leanh::lean_ctor_get(v___x_4178_, 0);
                    v_isSharedCheck_4246_ = (!crate::leanh::lean_is_exclusive(v___x_4178_)) as u8;
                    if v_isSharedCheck_4246_ == 0 {
                        v___x_4241_ = v___x_4178_;
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4239_);
                        crate::leanh::lean_dec(v___x_4178_);
                        v___x_4241_ = crate::leanh::lean_box(0);
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_4183_ = crate::leanh::lean_ctor_get(v___x_4176_, 0);
                crate::leanh::lean_inc_ref(v_env_4183_);
                crate::leanh::lean_dec(v___x_4176_);
                v_lctx_4184_ = crate::leanh::lean_ctor_get(v___x_4177_, 0);
                v_isSharedCheck_4236_ = (!crate::leanh::lean_is_exclusive(v___x_4177_)) as u8;
                if v_isSharedCheck_4236_ == 0 {
                    v_unused_4237_ = crate::leanh::lean_ctor_get(v___x_4177_, 1);
                    crate::leanh::lean_dec(v_unused_4237_);
                    v___x_4186_ = v___x_4177_;
                    v_isShared_4187_ = v_isSharedCheck_4236_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_4184_);
                    crate::leanh::lean_dec(v___x_4177_);
                    v___x_4186_ = crate::leanh::lean_box(0);
                    v_isShared_4187_ = v_isSharedCheck_4236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4188_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
                v___x_4189_ = lean_st_ref_take(v___y_4172_);
                v_traceState_4190_ = crate::leanh::lean_ctor_get(v___x_4189_, 4);
                v_env_4191_ = crate::leanh::lean_ctor_get(v___x_4189_, 0);
                v_nextMacroScope_4192_ = crate::leanh::lean_ctor_get(v___x_4189_, 1);
                v_ngen_4193_ = crate::leanh::lean_ctor_get(v___x_4189_, 2);
                v_auxDeclNGen_4194_ = crate::leanh::lean_ctor_get(v___x_4189_, 3);
                v_cache_4195_ = crate::leanh::lean_ctor_get(v___x_4189_, 5);
                v_messages_4196_ = crate::leanh::lean_ctor_get(v___x_4189_, 6);
                v_infoState_4197_ = crate::leanh::lean_ctor_get(v___x_4189_, 7);
                v_snapshotTasks_4198_ = crate::leanh::lean_ctor_get(v___x_4189_, 8);
                v_isSharedCheck_4235_ = (!crate::leanh::lean_is_exclusive(v___x_4189_)) as u8;
                if v_isSharedCheck_4235_ == 0 {
                    v___x_4200_ = v___x_4189_;
                    v_isShared_4201_ = v_isSharedCheck_4235_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4198_);
                    crate::leanh::lean_inc(v_infoState_4197_);
                    crate::leanh::lean_inc(v_messages_4196_);
                    crate::leanh::lean_inc(v_cache_4195_);
                    crate::leanh::lean_inc(v_traceState_4190_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4194_);
                    crate::leanh::lean_inc(v_ngen_4193_);
                    crate::leanh::lean_inc(v_nextMacroScope_4192_);
                    crate::leanh::lean_inc(v_env_4191_);
                    crate::leanh::lean_dec(v___x_4189_);
                    v___x_4200_ = crate::leanh::lean_box(0);
                    v_isShared_4201_ = v_isSharedCheck_4235_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_4202_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4190_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4203_ = crate::leanh::lean_ctor_get(v_traceState_4190_, 0);
                v_isSharedCheck_4234_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4190_)) as u8;
                if v_isSharedCheck_4234_ == 0 {
                    v___x_4205_ = v_traceState_4190_;
                    v_isShared_4206_ = v_isSharedCheck_4234_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4203_);
                    crate::leanh::lean_dec(v_traceState_4190_);
                    v___x_4205_ = crate::leanh::lean_box(0);
                    v_isShared_4206_ = v_isSharedCheck_4234_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4207_ = (crate::leanh::lean_unbox(v_a_4179_) as u8);
                crate::leanh::lean_dec(v_a_4179_);
                v___x_4208_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4184_, v___x_4207_);
                crate::leanh::lean_dec_ref(v_lctx_4184_);
                crate::leanh::lean_inc_ref(v_options_4174_);
                v___x_4209_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4209_, 0, v_env_4183_);
                crate::leanh::lean_ctor_set(v___x_4209_, 1, v___x_4188_);
                crate::leanh::lean_ctor_set(v___x_4209_, 2, v___x_4208_);
                crate::leanh::lean_ctor_set(v___x_4209_, 3, v_options_4174_);
                if v_isShared_4187_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4186_, 3);
                    crate::leanh::lean_ctor_set(v___x_4186_, 1, v_msg_4167_);
                    crate::leanh::lean_ctor_set(v___x_4186_, 0, v___x_4209_);
                    v___x_4211_ = v___x_4186_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4233_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4233_, 1, v_msg_4167_);
                    v___x_4211_ = v_reuseFailAlloc_4233_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4212_ = crate::leanh::lean_box(0);
                v___x_4213_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
                v___x_4214_ = 0;
                v___x_4215_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4;
                v___x_4216_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4216_, 0, v_cls_4166_);
                crate::leanh::lean_ctor_set(v___x_4216_, 1, v___x_4212_);
                crate::leanh::lean_ctor_set(v___x_4216_, 2, v___x_4215_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4216_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4213_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4216_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4213_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4216_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4214_,
                );
                v___x_4217_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5;
                v___x_4218_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4218_, 0, v___x_4216_);
                crate::leanh::lean_ctor_set(v___x_4218_, 1, v___x_4211_);
                crate::leanh::lean_ctor_set(v___x_4218_, 2, v___x_4217_);
                crate::leanh::lean_inc(v_ref_4175_);
                v___x_4219_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4219_, 0, v_ref_4175_);
                crate::leanh::lean_ctor_set(v___x_4219_, 1, v___x_4218_);
                v___x_4220_ = l_Lean_PersistentArray_push___redArg(v_traces_4203_, v___x_4219_);
                if v_isShared_4206_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4205_, 0, v___x_4220_);
                    v___x_4222_ = v___x_4205_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4220_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4232_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4202_,
                    );
                    v___x_4222_ = v_reuseFailAlloc_4232_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4200_, 4, v___x_4222_);
                    v___x_4224_ = v___x_4200_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4231_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_env_4191_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 1, v_nextMacroScope_4192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 2, v_ngen_4193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 3, v_auxDeclNGen_4194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 4, v___x_4222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 5, v_cache_4195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 6, v_messages_4196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 7, v_infoState_4197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 8, v_snapshotTasks_4198_);
                    v___x_4224_ = v_reuseFailAlloc_4231_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4225_ = lean_st_ref_set(v___y_4172_, v___x_4224_);
                v___x_4226_ = crate::leanh::lean_box(0);
                v___x_4227_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4226_);
                crate::leanh::lean_ctor_set(v___x_4227_, 1, v___y_4168_);
                if v_isShared_4182_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4181_, 0, v___x_4227_);
                    v___x_4229_ = v___x_4181_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4230_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
                    v___x_4229_ = v_reuseFailAlloc_4230_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4229_;
            }
            9 => {
                if v_isShared_4242_ == 0 {
                    v___x_4244_ = v___x_4241_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4245_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
                    v___x_4244_ = v_reuseFailAlloc_4245_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7___boxed(
    mut v_cls_4247_: *mut crate::leanh::LeanObject,
    mut v_msg_4248_: *mut crate::leanh::LeanObject,
    mut v___y_4249_: *mut crate::leanh::LeanObject,
    mut v___y_4250_: *mut crate::leanh::LeanObject,
    mut v___y_4251_: *mut crate::leanh::LeanObject,
    mut v___y_4252_: *mut crate::leanh::LeanObject,
    mut v___y_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4255_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_4247_, v_msg_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
    crate::leanh::lean_dec(v___y_4253_);
    crate::leanh::lean_dec_ref(v___y_4252_);
    crate::leanh::lean_dec(v___y_4251_);
    crate::leanh::lean_dec_ref(v___y_4250_);
    return v_res_4255_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(
    mut v_keys_4256_: *mut crate::leanh::LeanObject,
    mut v_i_4257_: *mut crate::leanh::LeanObject,
    mut v_k_4258_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: u8 = 0;
    let mut v_k_x27_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: u8 = 0;
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4259_ = lean_array_get_size(v_keys_4256_);
                v___x_4260_ = lean_nat_dec_lt(v_i_4257_, v___x_4259_);
                if v___x_4260_ == 0 {
                    crate::leanh::lean_dec(v_i_4257_);
                    return v___x_4260_;
                } else {
                    v_k_x27_4261_ = lean_array_fget_borrowed(v_keys_4256_, v_i_4257_);
                    v___x_4262_ = l_Lean_instBEqExtraModUse_beq(v_k_4258_, v_k_x27_4261_);
                    if v___x_4262_ == 0 {
                        v___x_4263_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4264_ = lean_nat_add(v_i_4257_, v___x_4263_);
                        crate::leanh::lean_dec(v_i_4257_);
                        v_i_4257_ = v___x_4264_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4257_);
                        return v___x_4262_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg___boxed(
    mut v_keys_4266_: *mut crate::leanh::LeanObject,
    mut v_i_4267_: *mut crate::leanh::LeanObject,
    mut v_k_4268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4269_: u8 = 0;
    let mut v_r_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4269_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_4266_, v_i_4267_, v_k_4268_);
    crate::leanh::lean_dec_ref(v_k_4268_);
    crate::leanh::lean_dec_ref(v_keys_4266_);
    v_r_4270_ = crate::leanh::lean_box((v_res_4269_) as usize);
    return v_r_4270_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0()
-> usize {
    let mut v___x_4271_: usize = 0;
    let mut v___x_4272_: usize = 0;
    let mut v___x_4273_: usize = 0;
    v___x_4271_ = 5usize;
    v___x_4272_ = 1usize;
    v___x_4273_ = lean_usize_shift_left(v___x_4272_, v___x_4271_);
    return v___x_4273_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1()
-> usize {
    let mut v___x_4274_: usize = 0;
    let mut v___x_4275_: usize = 0;
    let mut v___x_4276_: usize = 0;
    v___x_4274_ = 1usize;
    v___x_4275_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0);
    v___x_4276_ = lean_usize_sub(v___x_4275_, v___x_4274_);
    return v___x_4276_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(
    mut v_x_4277_: *mut crate::leanh::LeanObject,
    mut v_x_4278_: usize,
    mut v_x_4279_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: usize = 0;
    let mut v___x_4283_: usize = 0;
    let mut v___x_4284_: usize = 0;
    let mut v_j_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: u8 = 0;
    let mut v_node_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: usize = 0;
    let mut v___x_4292_: u8 = 0;
    let mut v_ks_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4277_) == 0 {
                    v_es_4280_ = crate::leanh::lean_ctor_get(v_x_4277_, 0);
                    v___x_4281_ = crate::leanh::lean_box(2);
                    v___x_4282_ = 5usize;
                    v___x_4283_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1);
                    v___x_4284_ = lean_usize_land(v_x_4278_, v___x_4283_);
                    v_j_4285_ = lean_usize_to_nat(v___x_4284_);
                    v___x_4286_ = lean_array_get_borrowed(v___x_4281_, v_es_4280_, v_j_4285_);
                    crate::leanh::lean_dec(v_j_4285_);
                    match crate::leanh::lean_obj_tag(v___x_4286_) {
                        0 => {
                            v_key_4287_ = crate::leanh::lean_ctor_get(v___x_4286_, 0);
                            v___x_4288_ = l_Lean_instBEqExtraModUse_beq(v_x_4279_, v_key_4287_);
                            return v___x_4288_;
                        }
                        1 => {
                            v_node_4289_ = crate::leanh::lean_ctor_get(v___x_4286_, 0);
                            v___x_4290_ = lean_usize_shift_right(v_x_4278_, v___x_4282_);
                            v_x_4277_ = v_node_4289_;
                            v_x_4278_ = v___x_4290_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4292_ = 0;
                            return v___x_4292_;
                        }
                    }
                } else {
                    v_ks_4293_ = crate::leanh::lean_ctor_get(v_x_4277_, 0);
                    v___x_4294_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4295_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_ks_4293_, v___x_4294_, v_x_4279_);
                    return v___x_4295_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___boxed(
    mut v_x_4296_: *mut crate::leanh::LeanObject,
    mut v_x_4297_: *mut crate::leanh::LeanObject,
    mut v_x_4298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_29687__boxed_4299_: usize = 0;
    let mut v_res_4300_: u8 = 0;
    let mut v_r_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_29687__boxed_4299_ = crate::leanh::lean_unbox_usize(v_x_4297_);
    crate::leanh::lean_dec(v_x_4297_);
    v_res_4300_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_4296_, v_x_29687__boxed_4299_, v_x_4298_);
    crate::leanh::lean_dec_ref(v_x_4298_);
    crate::leanh::lean_dec_ref(v_x_4296_);
    v_r_4301_ = crate::leanh::lean_box((v_res_4300_) as usize);
    return v_r_4301_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(
    mut v_x_4302_: *mut crate::leanh::LeanObject,
    mut v_x_4303_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4304_: u64 = 0;
    let mut v___x_4305_: usize = 0;
    let mut v___x_4306_: u8 = 0;
    v___x_4304_ = l_Lean_instHashableExtraModUse_hash(v_x_4303_);
    v___x_4305_ = lean_uint64_to_usize(v___x_4304_);
    v___x_4306_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_4302_, v___x_4305_, v_x_4303_);
    return v___x_4306_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_x_4307_: *mut crate::leanh::LeanObject,
    mut v_x_4308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4309_: u8 = 0;
    let mut v_r_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4309_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_4307_, v_x_4308_);
    crate::leanh::lean_dec_ref(v_x_4308_);
    crate::leanh::lean_dec_ref(v_x_4307_);
    v_r_4310_ = crate::leanh::lean_box((v_res_4309_) as usize);
    return v_r_4310_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4313_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1;
    v___x_4314_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0;
    v___x_4315_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4314_,
        v___x_4313_,
    );
    return v___x_4315_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4320_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5;
    v___x_4321_ = l_Lean_stringToMessageData(v___x_4320_);
    return v___x_4321_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4323_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7;
    v___x_4324_ = l_Lean_stringToMessageData(v___x_4323_);
    return v___x_4324_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4325_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4;
    v___x_4326_ = l_Lean_stringToMessageData(v___x_4325_);
    return v___x_4326_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_4327_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4;
    v___x_4328_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4;
    v___x_4329_ = l_Lean_Name_append(v___x_4328_, v_cls_4327_);
    return v___x_4329_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4331_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11;
    v___x_4332_ = l_Lean_stringToMessageData(v___x_4331_);
    return v___x_4332_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4334_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13;
    v___x_4335_ = l_Lean_stringToMessageData(v___x_4334_);
    return v___x_4335_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(
    mut v_mod_4340_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4341_: u8,
    mut v_hint_4342_: *mut crate::leanh::LeanObject,
    mut v___y_4343_: *mut crate::leanh::LeanObject,
    mut v___y_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
    mut v___y_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4351_: u8 = 0;
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v_asyncMode_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4385_: u8 = 0;
    let mut v_unused_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: u8 = 0;
    let mut v_options_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4390_: u8 = 0;
    let mut v_inheritedTraceOptions_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: u8 = 0;
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: u8 = 0;
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4349_ = lean_st_ref_get(v___y_4347_);
                v_env_4350_ = crate::leanh::lean_ctor_get(v___x_4349_, 0);
                crate::leanh::lean_inc_ref(v_env_4350_);
                crate::leanh::lean_dec(v___x_4349_);
                v_isExporting_4351_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_4350_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_4350_);
                v___x_4352_ = lean_st_ref_get(v___y_4347_);
                v_env_4353_ = crate::leanh::lean_ctor_get(v___x_4352_, 0);
                crate::leanh::lean_inc_ref(v_env_4353_);
                crate::leanh::lean_dec(v___x_4352_);
                v___x_4354_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2);
                crate::leanh::lean_inc(v_mod_4340_);
                v_entry_4355_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_4355_, 0, v_mod_4340_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_4355_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_4351_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_4355_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_4341_,
                );
                v___x_4356_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_4357_ = crate::leanh::lean_box(1);
                v___x_4358_ = crate::leanh::lean_box(0);
                v___x_4387_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4354_,
                    v___x_4356_,
                    v_env_4353_,
                    v___x_4357_,
                    v___x_4358_,
                );
                v___x_4388_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v___x_4387_, v_entry_4355_);
                crate::leanh::lean_dec(v___x_4387_);
                if v___x_4388_ == 0 {
                    v_options_4389_ = crate::leanh::lean_ctor_get(v___y_4346_, 2);
                    v_hasTrace_4390_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_4389_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4390_ == 0 {
                        crate::leanh::lean_dec(v_hint_4342_);
                        crate::leanh::lean_dec(v_mod_4340_);
                        v___y_4360_ = v___y_4343_;
                        v___y_4361_ = v___y_4347_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4391_ =
                            crate::leanh::lean_ctor_get(v___y_4346_, 13);
                        v_cls_4392_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4;
                        v___x_4414_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10);
                        v___x_4415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4391_,
                            v_options_4389_,
                            v___x_4414_,
                        );
                        if v___x_4415_ == 0 {
                            crate::leanh::lean_dec(v_hint_4342_);
                            crate::leanh::lean_dec(v_mod_4340_);
                            v___y_4360_ = v___y_4343_;
                            v___y_4361_ = v___y_4347_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4416_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12);
                            if v_isExporting_4351_ == 0 {
                                v___x_4425_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17;
                                v___y_4418_ = v___x_4425_;
                                state = 6;
                                continue;
                            } else {
                                v___x_4426_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18;
                                v___y_4418_ = v___x_4426_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_4355_, 1);
                    crate::leanh::lean_dec(v_hint_4342_);
                    crate::leanh::lean_dec(v_mod_4340_);
                    v___x_4427_ = crate::leanh::lean_box(0);
                    v___x_4428_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4428_, 0, v___x_4427_);
                    crate::leanh::lean_ctor_set(v___x_4428_, 1, v___y_4343_);
                    v___x_4429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4429_, 0, v___x_4428_);
                    return v___x_4429_;
                }
            }
            1 => {
                v___x_4362_ = lean_st_ref_take(v___y_4361_);
                v_toEnvExtension_4363_ = crate::leanh::lean_ctor_get(v___x_4356_, 0);
                v_env_4364_ = crate::leanh::lean_ctor_get(v___x_4362_, 0);
                v_nextMacroScope_4365_ = crate::leanh::lean_ctor_get(v___x_4362_, 1);
                v_ngen_4366_ = crate::leanh::lean_ctor_get(v___x_4362_, 2);
                v_auxDeclNGen_4367_ = crate::leanh::lean_ctor_get(v___x_4362_, 3);
                v_traceState_4368_ = crate::leanh::lean_ctor_get(v___x_4362_, 4);
                v_messages_4369_ = crate::leanh::lean_ctor_get(v___x_4362_, 6);
                v_infoState_4370_ = crate::leanh::lean_ctor_get(v___x_4362_, 7);
                v_snapshotTasks_4371_ = crate::leanh::lean_ctor_get(v___x_4362_, 8);
                v_isSharedCheck_4385_ = (!crate::leanh::lean_is_exclusive(v___x_4362_)) as u8;
                if v_isSharedCheck_4385_ == 0 {
                    v_unused_4386_ = crate::leanh::lean_ctor_get(v___x_4362_, 5);
                    crate::leanh::lean_dec(v_unused_4386_);
                    v___x_4373_ = v___x_4362_;
                    v_isShared_4374_ = v_isSharedCheck_4385_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4371_);
                    crate::leanh::lean_inc(v_infoState_4370_);
                    crate::leanh::lean_inc(v_messages_4369_);
                    crate::leanh::lean_inc(v_traceState_4368_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4367_);
                    crate::leanh::lean_inc(v_ngen_4366_);
                    crate::leanh::lean_inc(v_nextMacroScope_4365_);
                    crate::leanh::lean_inc(v_env_4364_);
                    crate::leanh::lean_dec(v___x_4362_);
                    v___x_4373_ = crate::leanh::lean_box(0);
                    v_isShared_4374_ = v_isSharedCheck_4385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4375_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4363_, 2);
                v___x_4376_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4356_,
                    v_env_4364_,
                    v_entry_4355_,
                    v_asyncMode_4375_,
                    v___x_4358_,
                );
                v___x_4377_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2,
                );
                if v_isShared_4374_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4373_, 5, v___x_4377_);
                    crate::leanh::lean_ctor_set(v___x_4373_, 0, v___x_4376_);
                    v___x_4379_ = v___x_4373_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4384_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4384_, 1, v_nextMacroScope_4365_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4384_, 2, v_ngen_4366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4384_, 3, v_auxDeclNGen_4367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4384_, 4, v_traceState_4368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4384_, 5, v___x_4377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4384_, 6, v_messages_4369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4384_, 7, v_infoState_4370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4384_, 8, v_snapshotTasks_4371_);
                    v___x_4379_ = v_reuseFailAlloc_4384_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4380_ = lean_st_ref_set(v___y_4361_, v___x_4379_);
                v___x_4381_ = crate::leanh::lean_box(0);
                v___x_4382_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4382_, 0, v___x_4381_);
                crate::leanh::lean_ctor_set(v___x_4382_, 1, v___y_4360_);
                v___x_4383_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4383_, 0, v___x_4382_);
                return v___x_4383_;
            }
            4 => {
                v___x_4396_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4396_, 0, v___y_4394_);
                crate::leanh::lean_ctor_set(v___x_4396_, 1, v___y_4395_);
                v___x_4397_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_4392_, v___x_4396_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
                if crate::leanh::lean_obj_tag(v___x_4397_) == 0 {
                    v_a_4398_ = crate::leanh::lean_ctor_get(v___x_4397_, 0);
                    crate::leanh::lean_inc(v_a_4398_);
                    crate::leanh::lean_dec_ref_known(v___x_4397_, 1);
                    v_snd_4399_ = crate::leanh::lean_ctor_get(v_a_4398_, 1);
                    crate::leanh::lean_inc(v_snd_4399_);
                    crate::leanh::lean_dec(v_a_4398_);
                    v___y_4360_ = v_snd_4399_;
                    v___y_4361_ = v___y_4347_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_4355_, 1);
                    return v___x_4397_;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_4402_);
                v___x_4403_ = l_Lean_stringToMessageData(v___y_4402_);
                v___x_4404_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4404_, 0, v___y_4401_);
                crate::leanh::lean_ctor_set(v___x_4404_, 1, v___x_4403_);
                v___x_4405_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6);
                v___x_4406_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4406_, 0, v___x_4404_);
                crate::leanh::lean_ctor_set(v___x_4406_, 1, v___x_4405_);
                v___x_4407_ = l_Lean_MessageData_ofName(v_mod_4340_);
                v___x_4408_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4408_, 0, v___x_4406_);
                crate::leanh::lean_ctor_set(v___x_4408_, 1, v___x_4407_);
                v___x_4409_ = l_Lean_Name_isAnonymous(v_hint_4342_);
                if v___x_4409_ == 0 {
                    v___x_4410_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8);
                    v___x_4411_ = l_Lean_MessageData_ofName(v_hint_4342_);
                    v___x_4412_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4412_, 0, v___x_4410_);
                    crate::leanh::lean_ctor_set(v___x_4412_, 1, v___x_4411_);
                    v___y_4394_ = v___x_4408_;
                    v___y_4395_ = v___x_4412_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_4342_);
                    v___x_4413_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9);
                    v___y_4394_ = v___x_4408_;
                    v___y_4395_ = v___x_4413_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_4418_);
                v___x_4419_ = l_Lean_stringToMessageData(v___y_4418_);
                v___x_4420_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4420_, 0, v___x_4416_);
                crate::leanh::lean_ctor_set(v___x_4420_, 1, v___x_4419_);
                v___x_4421_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14);
                v___x_4422_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4422_, 0, v___x_4420_);
                crate::leanh::lean_ctor_set(v___x_4422_, 1, v___x_4421_);
                if v_isMeta_4341_ == 0 {
                    v___x_4423_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15;
                    v___y_4401_ = v___x_4422_;
                    v___y_4402_ = v___x_4423_;
                    state = 5;
                    continue;
                } else {
                    v___x_4424_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16;
                    v___y_4401_ = v___x_4422_;
                    v___y_4402_ = v___x_4424_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___boxed(
    mut v_mod_4430_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4431_: *mut crate::leanh::LeanObject,
    mut v_hint_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
    mut v___y_4434_: *mut crate::leanh::LeanObject,
    mut v___y_4435_: *mut crate::leanh::LeanObject,
    mut v___y_4436_: *mut crate::leanh::LeanObject,
    mut v___y_4437_: *mut crate::leanh::LeanObject,
    mut v___y_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_4439_: u8 = 0;
    let mut v_res_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4439_ = (crate::leanh::lean_unbox(v_isMeta_4431_) as u8);
    v_res_4440_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_mod_4430_, v_isMeta_boxed_4439_, v_hint_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
    crate::leanh::lean_dec(v___y_4437_);
    crate::leanh::lean_dec_ref(v___y_4436_);
    crate::leanh::lean_dec(v___y_4435_);
    crate::leanh::lean_dec_ref(v___y_4434_);
    return v_res_4440_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(
    mut v_a_4441_: *mut crate::leanh::LeanObject,
    mut v_x_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u8 = 0;
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4442_) == 0 {
                    v___x_4443_ = crate::leanh::lean_box(0);
                    return v___x_4443_;
                } else {
                    v_key_4444_ = crate::leanh::lean_ctor_get(v_x_4442_, 0);
                    v_value_4445_ = crate::leanh::lean_ctor_get(v_x_4442_, 1);
                    v_tail_4446_ = crate::leanh::lean_ctor_get(v_x_4442_, 2);
                    v___x_4447_ = lean_name_eq(v_key_4444_, v_a_4441_);
                    if v___x_4447_ == 0 {
                        v_x_4442_ = v_tail_4446_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_4445_);
                        v___x_4449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4449_, 0, v_value_4445_);
                        return v___x_4449_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg___boxed(
    mut v_a_4450_: *mut crate::leanh::LeanObject,
    mut v_x_4451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4452_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_4450_, v_x_4451_);
    crate::leanh::lean_dec(v_x_4451_);
    crate::leanh::lean_dec(v_a_4450_);
    return v_res_4452_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: u64 = 0;
    v___x_4453_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4454_ = lean_uint64_of_nat(v___x_4453_);
    return v___x_4454_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(
    mut v_m_4455_: *mut crate::leanh::LeanObject,
    mut v_a_4456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4460_: u64 = 0;
    let mut v___x_4461_: u64 = 0;
    let mut v___x_4462_: u64 = 0;
    let mut v_fold_4463_: u64 = 0;
    let mut v___x_4464_: u64 = 0;
    let mut v___x_4465_: u64 = 0;
    let mut v___x_4466_: u64 = 0;
    let mut v___x_4467_: usize = 0;
    let mut v___x_4468_: usize = 0;
    let mut v___x_4469_: usize = 0;
    let mut v___x_4470_: usize = 0;
    let mut v___x_4471_: usize = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: u64 = 0;
    let mut v_hash_4475_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4457_ = crate::leanh::lean_ctor_get(v_m_4455_, 1);
                v___x_4458_ = lean_array_get_size(v_buckets_4457_);
                if crate::leanh::lean_obj_tag(v_a_4456_) == 0 {
                    v___x_4474_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0);
                    v___y_4460_ = v___x_4474_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4475_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_4456_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4460_ = v_hash_4475_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4461_ = 32u64;
                v___x_4462_ = lean_uint64_shift_right(v___y_4460_, v___x_4461_);
                v_fold_4463_ = lean_uint64_xor(v___y_4460_, v___x_4462_);
                v___x_4464_ = 16u64;
                v___x_4465_ = lean_uint64_shift_right(v_fold_4463_, v___x_4464_);
                v___x_4466_ = lean_uint64_xor(v_fold_4463_, v___x_4465_);
                v___x_4467_ = lean_uint64_to_usize(v___x_4466_);
                v___x_4468_ = lean_usize_of_nat(v___x_4458_);
                v___x_4469_ = 1usize;
                v___x_4470_ = lean_usize_sub(v___x_4468_, v___x_4469_);
                v___x_4471_ = lean_usize_land(v___x_4467_, v___x_4470_);
                v___x_4472_ = lean_array_uget_borrowed(v_buckets_4457_, v___x_4471_);
                v___x_4473_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_4456_, v___x_4472_);
                return v___x_4473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___boxed(
    mut v_m_4476_: *mut crate::leanh::LeanObject,
    mut v_a_4477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_4476_, v_a_4477_);
    crate::leanh::lean_dec(v_a_4477_);
    crate::leanh::lean_dec_ref(v_m_4476_);
    return v_res_4478_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(
    mut v___x_4479_: *mut crate::leanh::LeanObject,
    mut v_declName_4480_: *mut crate::leanh::LeanObject,
    mut v_as_4481_: *mut crate::leanh::LeanObject,
    mut v_sz_4482_: usize,
    mut v_i_4483_: usize,
    mut v_b_4484_: *mut crate::leanh::LeanObject,
    mut v___y_4485_: *mut crate::leanh::LeanObject,
    mut v___y_4486_: *mut crate::leanh::LeanObject,
    mut v___y_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
    mut v___y_4489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4491_: u8 = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: usize = 0;
    let mut v___x_4507_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4491_ = lean_usize_dec_lt(v_i_4483_, v_sz_4482_);
                if v___x_4491_ == 0 {
                    crate::leanh::lean_dec(v_declName_4480_);
                    v___x_4492_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4492_, 0, v_b_4484_);
                    crate::leanh::lean_ctor_set(v___x_4492_, 1, v___y_4485_);
                    v___x_4493_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4493_, 0, v___x_4492_);
                    return v___x_4493_;
                } else {
                    v___x_4494_ = l_Lean_Environment_header(v___x_4479_);
                    v_modules_4495_ = crate::leanh::lean_ctor_get(v___x_4494_, 3);
                    crate::leanh::lean_inc_ref(v_modules_4495_);
                    crate::leanh::lean_dec_ref(v___x_4494_);
                    v___x_4496_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_4497_ = lean_array_uget_borrowed(v_as_4481_, v_i_4483_);
                    v___x_4498_ = lean_array_get(v___x_4496_, v_modules_4495_, v_a_4497_);
                    crate::leanh::lean_dec_ref(v_modules_4495_);
                    v_toImport_4499_ = crate::leanh::lean_ctor_get(v___x_4498_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_4499_);
                    crate::leanh::lean_dec(v___x_4498_);
                    v_module_4500_ = crate::leanh::lean_ctor_get(v_toImport_4499_, 0);
                    crate::leanh::lean_inc(v_module_4500_);
                    crate::leanh::lean_dec_ref(v_toImport_4499_);
                    v___x_4501_ = 0;
                    crate::leanh::lean_inc(v_declName_4480_);
                    v___x_4502_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_4500_, v___x_4501_, v_declName_4480_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
                    if crate::leanh::lean_obj_tag(v___x_4502_) == 0 {
                        v_a_4503_ = crate::leanh::lean_ctor_get(v___x_4502_, 0);
                        crate::leanh::lean_inc(v_a_4503_);
                        crate::leanh::lean_dec_ref_known(v___x_4502_, 1);
                        v_snd_4504_ = crate::leanh::lean_ctor_get(v_a_4503_, 1);
                        crate::leanh::lean_inc(v_snd_4504_);
                        crate::leanh::lean_dec(v_a_4503_);
                        v___x_4505_ = crate::leanh::lean_box(0);
                        v___x_4506_ = 1usize;
                        v___x_4507_ = lean_usize_add(v_i_4483_, v___x_4506_);
                        v_i_4483_ = v___x_4507_;
                        v_b_4484_ = v___x_4505_;
                        v___y_4485_ = v_snd_4504_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_4480_);
                        return v___x_4502_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4___boxed(
    mut v___x_4509_: *mut crate::leanh::LeanObject,
    mut v_declName_4510_: *mut crate::leanh::LeanObject,
    mut v_as_4511_: *mut crate::leanh::LeanObject,
    mut v_sz_4512_: *mut crate::leanh::LeanObject,
    mut v_i_4513_: *mut crate::leanh::LeanObject,
    mut v_b_4514_: *mut crate::leanh::LeanObject,
    mut v___y_4515_: *mut crate::leanh::LeanObject,
    mut v___y_4516_: *mut crate::leanh::LeanObject,
    mut v___y_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4521_: usize = 0;
    let mut v_i_boxed_4522_: usize = 0;
    let mut v_res_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4521_ = crate::leanh::lean_unbox_usize(v_sz_4512_);
    crate::leanh::lean_dec(v_sz_4512_);
    v_i_boxed_4522_ = crate::leanh::lean_unbox_usize(v_i_4513_);
    crate::leanh::lean_dec(v_i_4513_);
    v_res_4523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v___x_4509_, v_declName_4510_, v_as_4511_, v_sz_boxed_4521_, v_i_boxed_4522_, v_b_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
    crate::leanh::lean_dec(v___y_4519_);
    crate::leanh::lean_dec_ref(v___y_4518_);
    crate::leanh::lean_dec(v___y_4517_);
    crate::leanh::lean_dec_ref(v___y_4516_);
    crate::leanh::lean_dec_ref(v_as_4511_);
    crate::leanh::lean_dec_ref(v___x_4509_);
    return v_res_4523_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4526_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1;
    v___x_4527_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0;
    v___x_4528_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4527_,
        v___x_4526_,
    );
    return v___x_4528_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(
    mut v_declName_4531_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4532_: u8,
    mut v___y_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4549_: usize = 0;
    let mut v___x_4550_: usize = 0;
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v_snd_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4559_: u8 = 0;
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4566_: u8 = 0;
    let mut v_unused_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: u8 = 0;
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4580_: u8 = 0;
    let mut v_toImport_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: u8 = 0;
    let mut v___x_4594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4539_ = lean_st_ref_get(v___y_4537_);
                v_env_4544_ = crate::leanh::lean_ctor_get(v___x_4539_, 0);
                crate::leanh::lean_inc_ref(v_env_4544_);
                crate::leanh::lean_dec(v___x_4539_);
                v___x_4569_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4544_, v_declName_4531_);
                if crate::leanh::lean_obj_tag(v___x_4569_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_4544_);
                    crate::leanh::lean_dec(v_declName_4531_);
                    state = 1;
                    continue;
                } else {
                    v_val_4570_ = crate::leanh::lean_ctor_get(v___x_4569_, 0);
                    crate::leanh::lean_inc(v_val_4570_);
                    crate::leanh::lean_dec_ref_known(v___x_4569_, 1);
                    v___x_4571_ = l_Lean_Environment_header(v_env_4544_);
                    v_modules_4572_ = crate::leanh::lean_ctor_get(v___x_4571_, 3);
                    crate::leanh::lean_inc_ref(v_modules_4572_);
                    crate::leanh::lean_dec_ref(v___x_4571_);
                    v___x_4573_ = lean_array_get_size(v_modules_4572_);
                    v___x_4574_ = lean_nat_dec_lt(v_val_4570_, v___x_4573_);
                    if v___x_4574_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_4572_);
                        crate::leanh::lean_dec(v_val_4570_);
                        crate::leanh::lean_dec_ref(v_env_4544_);
                        crate::leanh::lean_dec(v_declName_4531_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4575_ = lean_st_ref_get(v___y_4537_);
                        v_env_4576_ = crate::leanh::lean_ctor_get(v___x_4575_, 0);
                        crate::leanh::lean_inc_ref(v_env_4576_);
                        crate::leanh::lean_dec(v___x_4575_);
                        v___x_4577_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2);
                        v___x_4578_ = lean_array_fget(v_modules_4572_, v_val_4570_);
                        crate::leanh::lean_dec(v_val_4570_);
                        crate::leanh::lean_dec_ref(v_modules_4572_);
                        if v_isMeta_4532_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_4576_);
                            v___y_4580_ = v_isMeta_4532_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_4531_);
                            v___x_4593_ = l_Lean_isMarkedMeta(v_env_4576_, v_declName_4531_);
                            if v___x_4593_ == 0 {
                                v___y_4580_ = v_isMeta_4532_;
                                state = 7;
                                continue;
                            } else {
                                v___x_4594_ = 0;
                                v___y_4580_ = v___x_4594_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4541_ = crate::leanh::lean_box(0);
                v___x_4542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4542_, 0, v___x_4541_);
                crate::leanh::lean_ctor_set(v___x_4542_, 1, v___y_4533_);
                v___x_4543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4543_, 0, v___x_4542_);
                return v___x_4543_;
            }
            2 => {
                v___x_4548_ = crate::leanh::lean_box(0);
                v_sz_4549_ = lean_array_size(v___y_4547_);
                v___x_4550_ = 0usize;
                v___x_4551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v_env_4544_, v_declName_4531_, v___y_4547_, v_sz_4549_, v___x_4550_, v___x_4548_, v___y_4546_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
                crate::leanh::lean_dec_ref(v___y_4547_);
                crate::leanh::lean_dec_ref(v_env_4544_);
                if crate::leanh::lean_obj_tag(v___x_4551_) == 0 {
                    v_a_4552_ = crate::leanh::lean_ctor_get(v___x_4551_, 0);
                    v_isSharedCheck_4568_ = (!crate::leanh::lean_is_exclusive(v___x_4551_)) as u8;
                    if v_isSharedCheck_4568_ == 0 {
                        v___x_4554_ = v___x_4551_;
                        v_isShared_4555_ = v_isSharedCheck_4568_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4552_);
                        crate::leanh::lean_dec(v___x_4551_);
                        v___x_4554_ = crate::leanh::lean_box(0);
                        v_isShared_4555_ = v_isSharedCheck_4568_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4551_;
                }
            }
            3 => {
                v_snd_4556_ = crate::leanh::lean_ctor_get(v_a_4552_, 1);
                v_isSharedCheck_4566_ = (!crate::leanh::lean_is_exclusive(v_a_4552_)) as u8;
                if v_isSharedCheck_4566_ == 0 {
                    v_unused_4567_ = crate::leanh::lean_ctor_get(v_a_4552_, 0);
                    crate::leanh::lean_dec(v_unused_4567_);
                    v___x_4558_ = v_a_4552_;
                    v_isShared_4559_ = v_isSharedCheck_4566_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4556_);
                    crate::leanh::lean_dec(v_a_4552_);
                    v___x_4558_ = crate::leanh::lean_box(0);
                    v_isShared_4559_ = v_isSharedCheck_4566_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4559_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4558_, 0, v___x_4548_);
                    v___x_4561_ = v___x_4558_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4565_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4548_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_snd_4556_);
                    v___x_4561_ = v_reuseFailAlloc_4565_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4555_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4554_, 0, v___x_4561_);
                    v___x_4563_ = v___x_4554_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
                    v___x_4563_ = v_reuseFailAlloc_4564_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4563_;
            }
            7 => {
                v_toImport_4581_ = crate::leanh::lean_ctor_get(v___x_4578_, 0);
                crate::leanh::lean_inc_ref(v_toImport_4581_);
                crate::leanh::lean_dec(v___x_4578_);
                v_module_4582_ = crate::leanh::lean_ctor_get(v_toImport_4581_, 0);
                crate::leanh::lean_inc(v_module_4582_);
                crate::leanh::lean_dec_ref(v_toImport_4581_);
                crate::leanh::lean_inc(v_declName_4531_);
                v___x_4583_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_4582_, v___y_4580_, v_declName_4531_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
                if crate::leanh::lean_obj_tag(v___x_4583_) == 0 {
                    v_a_4584_ = crate::leanh::lean_ctor_get(v___x_4583_, 0);
                    crate::leanh::lean_inc(v_a_4584_);
                    crate::leanh::lean_dec_ref_known(v___x_4583_, 1);
                    v_snd_4585_ = crate::leanh::lean_ctor_get(v_a_4584_, 1);
                    crate::leanh::lean_inc(v_snd_4585_);
                    crate::leanh::lean_dec(v_a_4584_);
                    v___x_4586_ = l_Lean_indirectModUseExt;
                    v___x_4587_ = crate::leanh::lean_box(1);
                    v___x_4588_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_4544_);
                    v___x_4589_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4577_,
                        v___x_4586_,
                        v_env_4544_,
                        v___x_4587_,
                        v___x_4588_,
                    );
                    v___x_4590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v___x_4589_, v_declName_4531_);
                    crate::leanh::lean_dec(v___x_4589_);
                    if crate::leanh::lean_obj_tag(v___x_4590_) == 0 {
                        v___x_4591_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3;
                        v___y_4546_ = v_snd_4585_;
                        v___y_4547_ = v___x_4591_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4592_ = crate::leanh::lean_ctor_get(v___x_4590_, 0);
                        crate::leanh::lean_inc(v_val_4592_);
                        crate::leanh::lean_dec_ref_known(v___x_4590_, 1);
                        v___y_4546_ = v_snd_4585_;
                        v___y_4547_ = v_val_4592_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_4544_);
                    crate::leanh::lean_dec(v_declName_4531_);
                    return v___x_4583_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(
    mut v_declName_4595_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
    mut v___y_4601_: *mut crate::leanh::LeanObject,
    mut v___y_4602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_4603_: u8 = 0;
    let mut v_res_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4603_ = (crate::leanh::lean_unbox(v_isMeta_4596_) as u8);
    v_res_4604_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(v_declName_4595_, v_isMeta_boxed_4603_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
    crate::leanh::lean_dec(v___y_4601_);
    crate::leanh::lean_dec_ref(v___y_4600_);
    crate::leanh::lean_dec(v___y_4599_);
    crate::leanh::lean_dec_ref(v___y_4598_);
    return v_res_4604_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(
    mut v_keys_4605_: *mut crate::leanh::LeanObject,
    mut v_vals_4606_: *mut crate::leanh::LeanObject,
    mut v_i_4607_: *mut crate::leanh::LeanObject,
    mut v_k_4608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: u8 = 0;
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4609_ = lean_array_get_size(v_keys_4605_);
                v___x_4610_ = lean_nat_dec_lt(v_i_4607_, v___x_4609_);
                if v___x_4610_ == 0 {
                    crate::leanh::lean_dec(v_i_4607_);
                    v___x_4611_ = crate::leanh::lean_box(0);
                    return v___x_4611_;
                } else {
                    v_k_x27_4612_ = lean_array_fget_borrowed(v_keys_4605_, v_i_4607_);
                    v___x_4613_ = lean_name_eq(v_k_4608_, v_k_x27_4612_);
                    if v___x_4613_ == 0 {
                        v___x_4614_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4615_ = lean_nat_add(v_i_4607_, v___x_4614_);
                        crate::leanh::lean_dec(v_i_4607_);
                        v_i_4607_ = v___x_4615_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4617_ = lean_array_fget_borrowed(v_vals_4606_, v_i_4607_);
                        crate::leanh::lean_dec(v_i_4607_);
                        crate::leanh::lean_inc(v___x_4617_);
                        v___x_4618_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4618_, 0, v___x_4617_);
                        return v___x_4618_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_keys_4619_: *mut crate::leanh::LeanObject,
    mut v_vals_4620_: *mut crate::leanh::LeanObject,
    mut v_i_4621_: *mut crate::leanh::LeanObject,
    mut v_k_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4623_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_4619_, v_vals_4620_, v_i_4621_, v_k_4622_);
    crate::leanh::lean_dec(v_k_4622_);
    crate::leanh::lean_dec_ref(v_vals_4620_);
    crate::leanh::lean_dec_ref(v_keys_4619_);
    return v_res_4623_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(
    mut v_x_4624_: *mut crate::leanh::LeanObject,
    mut v_x_4625_: usize,
    mut v_x_4626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: usize = 0;
    let mut v___x_4630_: usize = 0;
    let mut v___x_4631_: usize = 0;
    let mut v_j_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: u8 = 0;
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: usize = 0;
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4624_) == 0 {
                    v_es_4627_ = crate::leanh::lean_ctor_get(v_x_4624_, 0);
                    v___x_4628_ = crate::leanh::lean_box(2);
                    v___x_4629_ = 5usize;
                    v___x_4630_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1);
                    v___x_4631_ = lean_usize_land(v_x_4625_, v___x_4630_);
                    v_j_4632_ = lean_usize_to_nat(v___x_4631_);
                    v___x_4633_ = lean_array_get_borrowed(v___x_4628_, v_es_4627_, v_j_4632_);
                    crate::leanh::lean_dec(v_j_4632_);
                    match crate::leanh::lean_obj_tag(v___x_4633_) {
                        0 => {
                            v_key_4634_ = crate::leanh::lean_ctor_get(v___x_4633_, 0);
                            v_val_4635_ = crate::leanh::lean_ctor_get(v___x_4633_, 1);
                            v___x_4636_ = lean_name_eq(v_x_4626_, v_key_4634_);
                            if v___x_4636_ == 0 {
                                v___x_4637_ = crate::leanh::lean_box(0);
                                return v___x_4637_;
                            } else {
                                crate::leanh::lean_inc(v_val_4635_);
                                v___x_4638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4638_, 0, v_val_4635_);
                                return v___x_4638_;
                            }
                        }
                        1 => {
                            v_node_4639_ = crate::leanh::lean_ctor_get(v___x_4633_, 0);
                            v___x_4640_ = lean_usize_shift_right(v_x_4625_, v___x_4629_);
                            v_x_4624_ = v_node_4639_;
                            v_x_4625_ = v___x_4640_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4642_ = crate::leanh::lean_box(0);
                            return v___x_4642_;
                        }
                    }
                } else {
                    v_ks_4643_ = crate::leanh::lean_ctor_get(v_x_4624_, 0);
                    v_vs_4644_ = crate::leanh::lean_ctor_get(v_x_4624_, 1);
                    v___x_4645_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4646_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_ks_4643_, v_vs_4644_, v___x_4645_, v_x_4626_);
                    return v___x_4646_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg___boxed(
    mut v_x_4647_: *mut crate::leanh::LeanObject,
    mut v_x_4648_: *mut crate::leanh::LeanObject,
    mut v_x_4649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30267__boxed_4650_: usize = 0;
    let mut v_res_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30267__boxed_4650_ = crate::leanh::lean_unbox_usize(v_x_4648_);
    crate::leanh::lean_dec(v_x_4648_);
    v_res_4651_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_4647_, v_x_30267__boxed_4650_, v_x_4649_);
    crate::leanh::lean_dec(v_x_4649_);
    crate::leanh::lean_dec_ref(v_x_4647_);
    return v_res_4651_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(
    mut v_x_4652_: *mut crate::leanh::LeanObject,
    mut v_x_4653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4655_: u64 = 0;
    let mut v___x_4656_: usize = 0;
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: u64 = 0;
    let mut v_hash_4659_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4653_) == 0 {
                    v___x_4658_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0);
                    v___y_4655_ = v___x_4658_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4659_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4653_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4655_ = v_hash_4659_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4656_ = lean_uint64_to_usize(v___y_4655_);
                v___x_4657_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_4652_, v___x_4656_, v_x_4653_);
                return v___x_4657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg___boxed(
    mut v_x_4660_: *mut crate::leanh::LeanObject,
    mut v_x_4661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_4660_, v_x_4661_);
    crate::leanh::lean_dec(v_x_4661_);
    crate::leanh::lean_dec_ref(v_x_4660_);
    return v_res_4662_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4663_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1;
    v___x_4664_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0;
    v___x_4665_ = l_Lean_PersistentHashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4664_,
        v___x_4663_,
    );
    return v___x_4665_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4667_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1;
    v___x_4668_ = l_Lean_stringToMessageData(v___x_4667_);
    return v___x_4668_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4670_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3;
    v___x_4671_ = l_Lean_stringToMessageData(v___x_4670_);
    return v___x_4671_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4673_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5;
    v___x_4674_ = l_Lean_stringToMessageData(v___x_4673_);
    return v___x_4674_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4676_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7;
    v___x_4677_ = l_Lean_stringToMessageData(v___x_4676_);
    return v___x_4677_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(
    mut v_origDecl_4678_: *mut crate::leanh::LeanObject,
    mut v_init_4679_: *mut crate::leanh::LeanObject,
    mut v_x_4680_: *mut crate::leanh::LeanObject,
    mut v___y_4681_: *mut crate::leanh::LeanObject,
    mut v___y_4682_: *mut crate::leanh::LeanObject,
    mut v___y_4683_: *mut crate::leanh::LeanObject,
    mut v___y_4684_: *mut crate::leanh::LeanObject,
    mut v___y_4685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4695_: u8 = 0;
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: u8 = 0;
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4712_: u8 = 0;
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4721_: u8 = 0;
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4725_: u8 = 0;
    let mut v_toSignature_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: u8 = 0;
    let mut v___x_4729_: u8 = 0;
    let mut v_a_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4733_: u8 = 0;
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4768_: u8 = 0;
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut v_reuseFailAlloc_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: u8 = 0;
    let mut v_snd_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: u8 = 0;
    let mut v___y_4788_: u8 = 0;
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: u8 = 0;
    let mut v___x_4792_: u8 = 0;
    let mut v___x_4793_: u8 = 0;
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4803_: u8 = 0;
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: u8 = 0;
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExported_4812_: u8 = 0;
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_unused_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4680_) == 0 {
                    v_k_4687_ = crate::leanh::lean_ctor_get(v_x_4680_, 1);
                    crate::leanh::lean_inc(v_k_4687_);
                    v_l_4688_ = crate::leanh::lean_ctor_get(v_x_4680_, 3);
                    crate::leanh::lean_inc(v_l_4688_);
                    v_r_4689_ = crate::leanh::lean_ctor_get(v_x_4680_, 4);
                    crate::leanh::lean_inc(v_r_4689_);
                    crate::leanh::lean_dec_ref_known(v_x_4680_, 5);
                    crate::leanh::lean_inc_ref(v_origDecl_4678_);
                    v___x_4690_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_4678_, v_init_4679_, v_l_4688_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
                    if crate::leanh::lean_obj_tag(v___x_4690_) == 0 {
                        v_a_4691_ = crate::leanh::lean_ctor_get(v___x_4690_, 0);
                        crate::leanh::lean_inc(v_a_4691_);
                        crate::leanh::lean_dec_ref_known(v___x_4690_, 1);
                        v_snd_4692_ = crate::leanh::lean_ctor_get(v_a_4691_, 1);
                        v_isSharedCheck_4815_ = (!crate::leanh::lean_is_exclusive(v_a_4691_)) as u8;
                        if v_isSharedCheck_4815_ == 0 {
                            v_unused_4816_ = crate::leanh::lean_ctor_get(v_a_4691_, 0);
                            crate::leanh::lean_dec(v_unused_4816_);
                            v___x_4694_ = v_a_4691_;
                            v_isShared_4695_ = v_isSharedCheck_4815_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_4692_);
                            crate::leanh::lean_dec(v_a_4691_);
                            v___x_4694_ = crate::leanh::lean_box(0);
                            v_isShared_4695_ = v_isSharedCheck_4815_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_4689_);
                        crate::leanh::lean_dec(v_k_4687_);
                        crate::leanh::lean_dec_ref(v_origDecl_4678_);
                        return v___x_4690_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origDecl_4678_);
                    v___x_4817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4817_, 0, v_init_4679_);
                    v___x_4818_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4818_, 0, v___x_4817_);
                    crate::leanh::lean_ctor_set(v___x_4818_, 1, v___y_4681_);
                    v___x_4819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4819_, 0, v___x_4818_);
                    return v___x_4819_;
                }
            }
            1 => {
                v___x_4696_ = crate::leanh::lean_box(0);
                v___x_4697_ = l_Lean_NameSet_contains(v_snd_4692_, v_k_4687_);
                if v___x_4697_ == 0 {
                    v___x_4698_ = lean_st_ref_get(v___y_4685_);
                    v_env_4699_ = crate::leanh::lean_ctor_get(v___x_4698_, 0);
                    crate::leanh::lean_inc_ref(v_env_4699_);
                    crate::leanh::lean_dec(v___x_4698_);
                    v___x_4700_ = l_Lean_Compiler_LCNF_baseExt;
                    v_toEnvExtension_4701_ = crate::leanh::lean_ctor_get(v___x_4700_, 0);
                    v_asyncMode_4702_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4701_, 2);
                    crate::leanh::lean_inc(v_k_4687_);
                    v___x_4703_ = l_Lean_NameSet_insert(v_snd_4692_, v_k_4687_);
                    v___x_4704_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0);
                    v___x_4705_ = crate::leanh::lean_box(0);
                    v___x_4706_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_4704_,
                        v___x_4700_,
                        v_env_4699_,
                        v_asyncMode_4702_,
                        v___x_4705_,
                    );
                    v___x_4707_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v___x_4706_, v_k_4687_);
                    crate::leanh::lean_dec(v___x_4706_);
                    if crate::leanh::lean_obj_tag(v___x_4707_) == 1 {
                        crate::leanh::lean_del_object(v___x_4694_);
                        crate::leanh::lean_dec(v_k_4687_);
                        v_val_4708_ = crate::leanh::lean_ctor_get(v___x_4707_, 0);
                        crate::leanh::lean_inc_n(v_val_4708_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4707_, 1);
                        v___x_4709_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(
                            v_val_4708_,
                            v___y_4684_,
                            v___y_4685_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4709_) == 0 {
                            v_a_4710_ = crate::leanh::lean_ctor_get(v___x_4709_, 0);
                            crate::leanh::lean_inc(v_a_4710_);
                            crate::leanh::lean_dec_ref_known(v___x_4709_, 1);
                            v_toSignature_4726_ = crate::leanh::lean_ctor_get(v_val_4708_, 0);
                            v_name_4727_ = crate::leanh::lean_ctor_get(v_toSignature_4726_, 0);
                            v___x_4728_ = l_Lean_isPrivateName(v_name_4727_);
                            if v___x_4728_ == 0 {
                                crate::leanh::lean_dec(v_a_4710_);
                                v___y_4712_ = v___x_4728_;
                                state = 2;
                                continue;
                            } else {
                                v___x_4729_ = (crate::leanh::lean_unbox(v_a_4710_) as u8);
                                crate::leanh::lean_dec(v_a_4710_);
                                v___y_4712_ = v___x_4729_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_4708_);
                            crate::leanh::lean_dec(v___x_4703_);
                            crate::leanh::lean_dec(v_r_4689_);
                            crate::leanh::lean_dec_ref(v_origDecl_4678_);
                            v_a_4730_ = crate::leanh::lean_ctor_get(v___x_4709_, 0);
                            v_isSharedCheck_4737_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4709_)) as u8;
                            if v_isSharedCheck_4737_ == 0 {
                                v___x_4732_ = v___x_4709_;
                                v_isShared_4733_ = v_isSharedCheck_4737_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4730_);
                                crate::leanh::lean_dec(v___x_4709_);
                                v___x_4732_ = crate::leanh::lean_box(0);
                                v_isShared_4733_ = v_isSharedCheck_4737_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4707_);
                        v___x_4738_ = lean_st_ref_get(v___y_4685_);
                        v_env_4739_ = crate::leanh::lean_ctor_get(v___x_4738_, 0);
                        crate::leanh::lean_inc_ref(v_env_4739_);
                        crate::leanh::lean_dec(v___x_4738_);
                        v___x_4740_ =
                            l_Lean_Environment_getModuleIdxFor_x3f(v_env_4739_, v_k_4687_);
                        crate::leanh::lean_dec_ref(v_env_4739_);
                        if crate::leanh::lean_obj_tag(v___x_4740_) == 1 {
                            v_val_4741_ = crate::leanh::lean_ctor_get(v___x_4740_, 0);
                            crate::leanh::lean_inc(v_val_4741_);
                            crate::leanh::lean_dec_ref_known(v___x_4740_, 1);
                            v___x_4774_ = lean_st_ref_get(v___y_4685_);
                            v_env_4783_ = crate::leanh::lean_ctor_get(v___x_4774_, 0);
                            crate::leanh::lean_inc_ref(v_env_4783_);
                            crate::leanh::lean_dec(v___x_4774_);
                            v___x_4784_ = l_Lean_Environment_header(v_env_4783_);
                            crate::leanh::lean_dec_ref(v_env_4783_);
                            v_modules_4785_ = crate::leanh::lean_ctor_get(v___x_4784_, 3);
                            crate::leanh::lean_inc_ref(v_modules_4785_);
                            crate::leanh::lean_dec_ref(v___x_4784_);
                            v___x_4786_ = 1;
                            v___x_4808_ = lean_array_get_size(v_modules_4785_);
                            v___x_4809_ = lean_nat_dec_lt(v_val_4741_, v___x_4808_);
                            if v___x_4809_ == 0 {
                                crate::leanh::lean_dec_ref(v_modules_4785_);
                                v___y_4788_ = v___x_4697_;
                                state = 12;
                                continue;
                            } else {
                                v___x_4810_ = lean_array_fget(v_modules_4785_, v_val_4741_);
                                crate::leanh::lean_dec_ref(v_modules_4785_);
                                v_toImport_4811_ = crate::leanh::lean_ctor_get(v___x_4810_, 0);
                                crate::leanh::lean_inc_ref(v_toImport_4811_);
                                crate::leanh::lean_dec(v___x_4810_);
                                v_isExported_4812_ = crate::leanh::lean_ctor_get_uint8(
                                    v_toImport_4811_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1)
                                        as u32,
                                );
                                crate::leanh::lean_dec_ref(v_toImport_4811_);
                                if v_isExported_4812_ == 0 {
                                    state = 11;
                                    continue;
                                } else {
                                    v___y_4788_ = v___x_4697_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_4740_);
                            crate::leanh::lean_del_object(v___x_4694_);
                            crate::leanh::lean_dec(v_k_4687_);
                            v_init_4679_ = v___x_4696_;
                            v_x_4680_ = v_r_4689_;
                            v___y_4681_ = v___x_4703_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4694_);
                    crate::leanh::lean_dec(v_k_4687_);
                    v_init_4679_ = v___x_4696_;
                    v_x_4680_ = v_r_4689_;
                    v___y_4681_ = v_snd_4692_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_4712_ == 0 {
                    crate::leanh::lean_dec(v_val_4708_);
                    v_init_4679_ = v___x_4696_;
                    v_x_4680_ = v_r_4689_;
                    v___y_4681_ = v___x_4703_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_origDecl_4678_);
                    v___x_4714_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_4678_, v_val_4708_, v___x_4703_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
                    if crate::leanh::lean_obj_tag(v___x_4714_) == 0 {
                        v_a_4715_ = crate::leanh::lean_ctor_get(v___x_4714_, 0);
                        crate::leanh::lean_inc(v_a_4715_);
                        crate::leanh::lean_dec_ref_known(v___x_4714_, 1);
                        v_snd_4716_ = crate::leanh::lean_ctor_get(v_a_4715_, 1);
                        crate::leanh::lean_inc(v_snd_4716_);
                        crate::leanh::lean_dec(v_a_4715_);
                        v_init_4679_ = v___x_4696_;
                        v_x_4680_ = v_r_4689_;
                        v___y_4681_ = v_snd_4716_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_4689_);
                        crate::leanh::lean_dec_ref(v_origDecl_4678_);
                        v_a_4718_ = crate::leanh::lean_ctor_get(v___x_4714_, 0);
                        v_isSharedCheck_4725_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4714_)) as u8;
                        if v_isSharedCheck_4725_ == 0 {
                            v___x_4720_ = v___x_4714_;
                            v_isShared_4721_ = v_isSharedCheck_4725_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4718_);
                            crate::leanh::lean_dec(v___x_4714_);
                            v___x_4720_ = crate::leanh::lean_box(0);
                            v_isShared_4721_ = v_isSharedCheck_4725_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_4721_ == 0 {
                    v___x_4723_ = v___x_4720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
                    v___x_4723_ = v_reuseFailAlloc_4724_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4723_;
            }
            5 => {
                if v_isShared_4733_ == 0 {
                    v___x_4735_ = v___x_4732_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4736_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
                    v___x_4735_ = v_reuseFailAlloc_4736_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4735_;
            }
            7 => {
                v___x_4743_ = lean_st_ref_get(v___y_4685_);
                v_toSignature_4744_ = crate::leanh::lean_ctor_get(v_origDecl_4678_, 0);
                crate::leanh::lean_inc_ref(v_toSignature_4744_);
                crate::leanh::lean_dec_ref(v_origDecl_4678_);
                v_env_4745_ = crate::leanh::lean_ctor_get(v___x_4743_, 0);
                crate::leanh::lean_inc_ref(v_env_4745_);
                crate::leanh::lean_dec(v___x_4743_);
                v_name_4746_ = crate::leanh::lean_ctor_get(v_toSignature_4744_, 0);
                crate::leanh::lean_inc(v_name_4746_);
                crate::leanh::lean_dec_ref(v_toSignature_4744_);
                v___x_4747_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2);
                v___x_4748_ = l_Lean_MessageData_ofConstName(v_name_4746_, v___x_4697_);
                if v_isShared_4695_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4694_, 7);
                    crate::leanh::lean_ctor_set(v___x_4694_, 1, v___x_4748_);
                    crate::leanh::lean_ctor_set(v___x_4694_, 0, v___x_4747_);
                    v___x_4750_ = v___x_4694_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4773_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4773_, 1, v___x_4748_);
                    v___x_4750_ = v_reuseFailAlloc_4773_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4751_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4);
                v___x_4752_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4752_, 0, v___x_4750_);
                crate::leanh::lean_ctor_set(v___x_4752_, 1, v___x_4751_);
                v___x_4753_ = l_Lean_MessageData_ofConstName(v_k_4687_, v___x_4697_);
                v___x_4754_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4754_, 0, v___x_4752_);
                crate::leanh::lean_ctor_set(v___x_4754_, 1, v___x_4753_);
                v___x_4755_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6);
                v___x_4756_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4756_, 0, v___x_4754_);
                crate::leanh::lean_ctor_set(v___x_4756_, 1, v___x_4755_);
                v___x_4757_ = l_Lean_Environment_header(v_env_4745_);
                crate::leanh::lean_dec_ref(v_env_4745_);
                v___x_4758_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4757_);
                v___x_4759_ = lean_array_get(v___x_4705_, v___x_4758_, v_val_4741_);
                crate::leanh::lean_dec(v_val_4741_);
                crate::leanh::lean_dec_ref(v___x_4758_);
                v___x_4760_ = l_Lean_MessageData_ofName(v___x_4759_);
                v___x_4761_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4761_, 0, v___x_4756_);
                crate::leanh::lean_ctor_set(v___x_4761_, 1, v___x_4760_);
                v___x_4762_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8);
                v___x_4763_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4763_, 0, v___x_4761_);
                crate::leanh::lean_ctor_set(v___x_4763_, 1, v___x_4762_);
                v___x_4764_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_4763_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
                v_a_4765_ = crate::leanh::lean_ctor_get(v___x_4764_, 0);
                v_isSharedCheck_4772_ = (!crate::leanh::lean_is_exclusive(v___x_4764_)) as u8;
                if v_isSharedCheck_4772_ == 0 {
                    v___x_4767_ = v___x_4764_;
                    v_isShared_4768_ = v_isSharedCheck_4772_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4765_);
                    crate::leanh::lean_dec(v___x_4764_);
                    v___x_4767_ = crate::leanh::lean_box(0);
                    v_isShared_4768_ = v_isSharedCheck_4772_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4768_ == 0 {
                    v___x_4770_ = v___x_4767_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4771_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
                    v___x_4770_ = v_reuseFailAlloc_4771_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4770_;
            }
            11 => {
                v___x_4776_ = l_Lean_Compiler_compiler_inLeanIR;
                v___x_4777_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v___x_4776_, v___x_4703_, v___y_4684_);
                v_a_4778_ = crate::leanh::lean_ctor_get(v___x_4777_, 0);
                crate::leanh::lean_inc(v_a_4778_);
                crate::leanh::lean_dec_ref(v___x_4777_);
                v_fst_4779_ = crate::leanh::lean_ctor_get(v_a_4778_, 0);
                v___x_4780_ = (crate::leanh::lean_unbox(v_fst_4779_) as u8);
                if v___x_4780_ == 0 {
                    crate::leanh::lean_dec(v_a_4778_);
                    crate::leanh::lean_dec(v_r_4689_);
                    state = 7;
                    continue;
                } else {
                    if v___x_4697_ == 0 {
                        crate::leanh::lean_dec(v_val_4741_);
                        crate::leanh::lean_del_object(v___x_4694_);
                        crate::leanh::lean_dec(v_k_4687_);
                        v_snd_4781_ = crate::leanh::lean_ctor_get(v_a_4778_, 1);
                        crate::leanh::lean_inc(v_snd_4781_);
                        crate::leanh::lean_dec(v_a_4778_);
                        v_init_4679_ = v___x_4696_;
                        v_x_4680_ = v_r_4689_;
                        v___y_4681_ = v_snd_4781_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_4778_);
                        crate::leanh::lean_dec(v_r_4689_);
                        state = 7;
                        continue;
                    }
                }
            }
            12 => {
                if v___y_4788_ == 0 {
                    crate::leanh::lean_dec(v_val_4741_);
                    crate::leanh::lean_del_object(v___x_4694_);
                    v___x_4789_ = lean_st_ref_get(v___y_4685_);
                    v_env_4790_ = crate::leanh::lean_ctor_get(v___x_4789_, 0);
                    crate::leanh::lean_inc_ref(v_env_4790_);
                    crate::leanh::lean_dec(v___x_4789_);
                    crate::leanh::lean_inc(v_k_4687_);
                    v___x_4791_ = l_Lean_getIRPhases(v_env_4790_, v_k_4687_);
                    v___x_4792_ = 1;
                    v___x_4793_ = l_Lean_instBEqIRPhases_beq(v___x_4791_, v___x_4792_);
                    v___x_4794_ = crate::leanh::lean_box((v___x_4793_) as usize);
                    v___x_4795_ = crate::leanh::lean_alloc_closure(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed as *mut core::ffi::c_void, 8, 2);
                    crate::leanh::lean_closure_set(v___x_4795_, 0, v_k_4687_);
                    crate::leanh::lean_closure_set(v___x_4795_, 1, v___x_4794_);
                    v___x_4796_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v___x_4795_, v___x_4786_, v___x_4703_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
                    if crate::leanh::lean_obj_tag(v___x_4796_) == 0 {
                        v_a_4797_ = crate::leanh::lean_ctor_get(v___x_4796_, 0);
                        crate::leanh::lean_inc(v_a_4797_);
                        crate::leanh::lean_dec_ref_known(v___x_4796_, 1);
                        v_snd_4798_ = crate::leanh::lean_ctor_get(v_a_4797_, 1);
                        crate::leanh::lean_inc(v_snd_4798_);
                        crate::leanh::lean_dec(v_a_4797_);
                        v_init_4679_ = v___x_4696_;
                        v_x_4680_ = v_r_4689_;
                        v___y_4681_ = v_snd_4798_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_4689_);
                        crate::leanh::lean_dec_ref(v_origDecl_4678_);
                        v_a_4800_ = crate::leanh::lean_ctor_get(v___x_4796_, 0);
                        v_isSharedCheck_4807_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4796_)) as u8;
                        if v_isSharedCheck_4807_ == 0 {
                            v___x_4802_ = v___x_4796_;
                            v_isShared_4803_ = v_isSharedCheck_4807_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4800_);
                            crate::leanh::lean_dec(v___x_4796_);
                            v___x_4802_ = crate::leanh::lean_box(0);
                            v_isShared_4803_ = v_isSharedCheck_4807_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    state = 11;
                    continue;
                }
            }
            13 => {
                if v_isShared_4803_ == 0 {
                    v___x_4805_ = v___x_4802_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
                    v___x_4805_ = v_reuseFailAlloc_4806_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4805_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(
    mut v___x_4820_: u8,
    mut v_origDecl_4821_: *mut crate::leanh::LeanObject,
    mut v_code_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v_snd_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4840_: u8 = 0;
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4847_: u8 = 0;
    let mut v_unused_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut v_a_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4853_: u8 = 0;
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4829_ = l_Lean_NameSet_empty;
                v___x_4830_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v___x_4820_, v_code_4822_, v___x_4829_);
                v___x_4831_ = crate::leanh::lean_box(0);
                v___x_4832_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_4821_, v___x_4831_, v___x_4830_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
                if crate::leanh::lean_obj_tag(v___x_4832_) == 0 {
                    v_a_4833_ = crate::leanh::lean_ctor_get(v___x_4832_, 0);
                    v_isSharedCheck_4849_ = (!crate::leanh::lean_is_exclusive(v___x_4832_)) as u8;
                    if v_isSharedCheck_4849_ == 0 {
                        v___x_4835_ = v___x_4832_;
                        v_isShared_4836_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4833_);
                        crate::leanh::lean_dec(v___x_4832_);
                        v___x_4835_ = crate::leanh::lean_box(0);
                        v_isShared_4836_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4850_ = crate::leanh::lean_ctor_get(v___x_4832_, 0);
                    v_isSharedCheck_4857_ = (!crate::leanh::lean_is_exclusive(v___x_4832_)) as u8;
                    if v_isSharedCheck_4857_ == 0 {
                        v___x_4852_ = v___x_4832_;
                        v_isShared_4853_ = v_isSharedCheck_4857_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4850_);
                        crate::leanh::lean_dec(v___x_4832_);
                        v___x_4852_ = crate::leanh::lean_box(0);
                        v_isShared_4853_ = v_isSharedCheck_4857_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4837_ = crate::leanh::lean_ctor_get(v_a_4833_, 1);
                v_isSharedCheck_4847_ = (!crate::leanh::lean_is_exclusive(v_a_4833_)) as u8;
                if v_isSharedCheck_4847_ == 0 {
                    v_unused_4848_ = crate::leanh::lean_ctor_get(v_a_4833_, 0);
                    crate::leanh::lean_dec(v_unused_4848_);
                    v___x_4839_ = v_a_4833_;
                    v_isShared_4840_ = v_isSharedCheck_4847_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4837_);
                    crate::leanh::lean_dec(v_a_4833_);
                    v___x_4839_ = crate::leanh::lean_box(0);
                    v_isShared_4840_ = v_isSharedCheck_4847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4840_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4839_, 0, v___x_4831_);
                    v___x_4842_ = v___x_4839_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4846_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4846_, 1, v_snd_4837_);
                    v___x_4842_ = v_reuseFailAlloc_4846_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4836_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4835_, 0, v___x_4842_);
                    v___x_4844_ = v___x_4835_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4845_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4842_);
                    v___x_4844_ = v_reuseFailAlloc_4845_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4844_;
            }
            5 => {
                if v_isShared_4853_ == 0 {
                    v___x_4855_ = v___x_4852_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4856_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
                    v___x_4855_ = v_reuseFailAlloc_4856_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed(
    mut v___x_4858_: *mut crate::leanh::LeanObject,
    mut v_origDecl_4859_: *mut crate::leanh::LeanObject,
    mut v_code_4860_: *mut crate::leanh::LeanObject,
    mut v___y_4861_: *mut crate::leanh::LeanObject,
    mut v___y_4862_: *mut crate::leanh::LeanObject,
    mut v___y_4863_: *mut crate::leanh::LeanObject,
    mut v___y_4864_: *mut crate::leanh::LeanObject,
    mut v___y_4865_: *mut crate::leanh::LeanObject,
    mut v___y_4866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_30356__boxed_4867_: u8 = 0;
    let mut v_res_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_30356__boxed_4867_ = (crate::leanh::lean_unbox(v___x_4858_) as u8);
    v_res_4868_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(v___x_30356__boxed_4867_, v_origDecl_4859_, v_code_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
    crate::leanh::lean_dec(v___y_4865_);
    crate::leanh::lean_dec_ref(v___y_4864_);
    crate::leanh::lean_dec(v___y_4863_);
    crate::leanh::lean_dec_ref(v___y_4862_);
    return v_res_4868_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(
    mut v_origDecl_4869_: *mut crate::leanh::LeanObject,
    mut v_decl_4870_: *mut crate::leanh::LeanObject,
    mut v_a_4871_: *mut crate::leanh::LeanObject,
    mut v_a_4872_: *mut crate::leanh::LeanObject,
    mut v_a_4873_: *mut crate::leanh::LeanObject,
    mut v_a_4874_: *mut crate::leanh::LeanObject,
    mut v_a_4875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_value_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: u8 = 0;
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_value_4877_ = crate::leanh::lean_ctor_get(v_decl_4870_, 1);
    crate::leanh::lean_inc_ref(v_value_4877_);
    crate::leanh::lean_dec_ref(v_decl_4870_);
    v___x_4878_ = 0;
    v___x_4879_ = crate::leanh::lean_box((v___x_4878_) as usize);
    v___f_4880_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
    crate::leanh::lean_closure_set(v___f_4880_, 0, v___x_4879_);
    crate::leanh::lean_closure_set(v___f_4880_, 1, v_origDecl_4869_);
    v___x_4881_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_4880_, v_value_4877_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
    return v___x_4881_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___boxed(
    mut v_origDecl_4882_: *mut crate::leanh::LeanObject,
    mut v_decl_4883_: *mut crate::leanh::LeanObject,
    mut v_a_4884_: *mut crate::leanh::LeanObject,
    mut v_a_4885_: *mut crate::leanh::LeanObject,
    mut v_a_4886_: *mut crate::leanh::LeanObject,
    mut v_a_4887_: *mut crate::leanh::LeanObject,
    mut v_a_4888_: *mut crate::leanh::LeanObject,
    mut v_a_4889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4890_ =
        l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(
            v_origDecl_4882_,
            v_decl_4883_,
            v_a_4884_,
            v_a_4885_,
            v_a_4886_,
            v_a_4887_,
            v_a_4888_,
        );
    crate::leanh::lean_dec(v_a_4888_);
    crate::leanh::lean_dec_ref(v_a_4887_);
    crate::leanh::lean_dec(v_a_4886_);
    crate::leanh::lean_dec_ref(v_a_4885_);
    return v_res_4890_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___boxed(
    mut v_origDecl_4891_: *mut crate::leanh::LeanObject,
    mut v_init_4892_: *mut crate::leanh::LeanObject,
    mut v_x_4893_: *mut crate::leanh::LeanObject,
    mut v___y_4894_: *mut crate::leanh::LeanObject,
    mut v___y_4895_: *mut crate::leanh::LeanObject,
    mut v___y_4896_: *mut crate::leanh::LeanObject,
    mut v___y_4897_: *mut crate::leanh::LeanObject,
    mut v___y_4898_: *mut crate::leanh::LeanObject,
    mut v___y_4899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4900_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_4891_, v_init_4892_, v_x_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
    crate::leanh::lean_dec(v___y_4898_);
    crate::leanh::lean_dec_ref(v___y_4897_);
    crate::leanh::lean_dec(v___y_4896_);
    crate::leanh::lean_dec_ref(v___y_4895_);
    return v_res_4900_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(
    mut v_00_u03b2_4901_: *mut crate::leanh::LeanObject,
    mut v_x_4902_: *mut crate::leanh::LeanObject,
    mut v_x_4903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4904_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_4902_, v_x_4903_);
    return v___x_4904_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___boxed(
    mut v_00_u03b2_4905_: *mut crate::leanh::LeanObject,
    mut v_x_4906_: *mut crate::leanh::LeanObject,
    mut v_x_4907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4908_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(v_00_u03b2_4905_, v_x_4906_, v_x_4907_);
    crate::leanh::lean_dec(v_x_4907_);
    crate::leanh::lean_dec_ref(v_x_4906_);
    return v_res_4908_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(
    mut v_opt_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
    mut v___y_4911_: *mut crate::leanh::LeanObject,
    mut v___y_4912_: *mut crate::leanh::LeanObject,
    mut v___y_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4916_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_4909_, v___y_4910_, v___y_4913_);
    return v___x_4916_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(
    mut v_opt_4917_: *mut crate::leanh::LeanObject,
    mut v___y_4918_: *mut crate::leanh::LeanObject,
    mut v___y_4919_: *mut crate::leanh::LeanObject,
    mut v___y_4920_: *mut crate::leanh::LeanObject,
    mut v___y_4921_: *mut crate::leanh::LeanObject,
    mut v___y_4922_: *mut crate::leanh::LeanObject,
    mut v___y_4923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4924_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(v_opt_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_);
    crate::leanh::lean_dec(v___y_4922_);
    crate::leanh::lean_dec_ref(v___y_4921_);
    crate::leanh::lean_dec(v___y_4920_);
    crate::leanh::lean_dec_ref(v___y_4919_);
    crate::leanh::lean_dec_ref(v_opt_4917_);
    return v_res_4924_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(
    mut v_00_u03b2_4925_: *mut crate::leanh::LeanObject,
    mut v_x_4926_: *mut crate::leanh::LeanObject,
    mut v_x_4927_: usize,
    mut v_x_4928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4929_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_4926_, v_x_4927_, v_x_4928_);
    return v___x_4929_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_4930_: *mut crate::leanh::LeanObject,
    mut v_x_4931_: *mut crate::leanh::LeanObject,
    mut v_x_4932_: *mut crate::leanh::LeanObject,
    mut v_x_4933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30773__boxed_4934_: usize = 0;
    let mut v_res_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30773__boxed_4934_ = crate::leanh::lean_unbox_usize(v_x_4932_);
    crate::leanh::lean_dec(v_x_4932_);
    v_res_4935_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(v_00_u03b2_4930_, v_x_4931_, v_x_30773__boxed_4934_, v_x_4933_);
    crate::leanh::lean_dec(v_x_4933_);
    crate::leanh::lean_dec_ref(v_x_4931_);
    return v_res_4935_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(
    mut v_00_u03b2_4936_: *mut crate::leanh::LeanObject,
    mut v_m_4937_: *mut crate::leanh::LeanObject,
    mut v_a_4938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4939_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_4937_, v_a_4938_);
    return v___x_4939_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___boxed(
    mut v_00_u03b2_4940_: *mut crate::leanh::LeanObject,
    mut v_m_4941_: *mut crate::leanh::LeanObject,
    mut v_a_4942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(v_00_u03b2_4940_, v_m_4941_, v_a_4942_);
    crate::leanh::lean_dec(v_a_4942_);
    crate::leanh::lean_dec_ref(v_m_4941_);
    return v_res_4943_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4944_: *mut crate::leanh::LeanObject,
    mut v_keys_4945_: *mut crate::leanh::LeanObject,
    mut v_vals_4946_: *mut crate::leanh::LeanObject,
    mut v_heq_4947_: *mut crate::leanh::LeanObject,
    mut v_i_4948_: *mut crate::leanh::LeanObject,
    mut v_k_4949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4950_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_4945_, v_vals_4946_, v_i_4948_, v_k_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_4951_: *mut crate::leanh::LeanObject,
    mut v_keys_4952_: *mut crate::leanh::LeanObject,
    mut v_vals_4953_: *mut crate::leanh::LeanObject,
    mut v_heq_4954_: *mut crate::leanh::LeanObject,
    mut v_i_4955_: *mut crate::leanh::LeanObject,
    mut v_k_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(v_00_u03b2_4951_, v_keys_4952_, v_vals_4953_, v_heq_4954_, v_i_4955_, v_k_4956_);
    crate::leanh::lean_dec(v_k_4956_);
    crate::leanh::lean_dec_ref(v_vals_4953_);
    crate::leanh::lean_dec_ref(v_keys_4952_);
    return v_res_4957_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(
    mut v_00_u03b2_4958_: *mut crate::leanh::LeanObject,
    mut v_x_4959_: *mut crate::leanh::LeanObject,
    mut v_x_4960_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4961_: u8 = 0;
    v___x_4961_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_4959_, v_x_4960_);
    return v___x_4961_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b2_4962_: *mut crate::leanh::LeanObject,
    mut v_x_4963_: *mut crate::leanh::LeanObject,
    mut v_x_4964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4965_: u8 = 0;
    let mut v_r_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4965_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(v_00_u03b2_4962_, v_x_4963_, v_x_4964_);
    crate::leanh::lean_dec_ref(v_x_4964_);
    crate::leanh::lean_dec_ref(v_x_4963_);
    v_r_4966_ = crate::leanh::lean_box((v_res_4965_) as usize);
    return v_r_4966_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(
    mut v_00_u03b2_4967_: *mut crate::leanh::LeanObject,
    mut v_a_4968_: *mut crate::leanh::LeanObject,
    mut v_x_4969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4970_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_4968_, v_x_4969_);
    return v___x_4970_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___boxed(
    mut v_00_u03b2_4971_: *mut crate::leanh::LeanObject,
    mut v_a_4972_: *mut crate::leanh::LeanObject,
    mut v_x_4973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4974_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(v_00_u03b2_4971_, v_a_4972_, v_x_4973_);
    crate::leanh::lean_dec(v_x_4973_);
    crate::leanh::lean_dec(v_a_4972_);
    return v_res_4974_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(
    mut v_00_u03b2_4975_: *mut crate::leanh::LeanObject,
    mut v_x_4976_: *mut crate::leanh::LeanObject,
    mut v_x_4977_: usize,
    mut v_x_4978_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4979_: u8 = 0;
    v___x_4979_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_4976_, v_x_4977_, v_x_4978_);
    return v___x_4979_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___boxed(
    mut v_00_u03b2_4980_: *mut crate::leanh::LeanObject,
    mut v_x_4981_: *mut crate::leanh::LeanObject,
    mut v_x_4982_: *mut crate::leanh::LeanObject,
    mut v_x_4983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30801__boxed_4984_: usize = 0;
    let mut v_res_4985_: u8 = 0;
    let mut v_r_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30801__boxed_4984_ = crate::leanh::lean_unbox_usize(v_x_4982_);
    crate::leanh::lean_dec(v_x_4982_);
    v_res_4985_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_4980_, v_x_4981_, v_x_30801__boxed_4984_, v_x_4983_);
    crate::leanh::lean_dec_ref(v_x_4983_);
    crate::leanh::lean_dec_ref(v_x_4981_);
    v_r_4986_ = crate::leanh::lean_box((v_res_4985_) as usize);
    return v_r_4986_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(
    mut v_00_u03b2_4987_: *mut crate::leanh::LeanObject,
    mut v_keys_4988_: *mut crate::leanh::LeanObject,
    mut v_vals_4989_: *mut crate::leanh::LeanObject,
    mut v_heq_4990_: *mut crate::leanh::LeanObject,
    mut v_i_4991_: *mut crate::leanh::LeanObject,
    mut v_k_4992_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4993_: u8 = 0;
    v___x_4993_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_4988_, v_i_4991_, v_k_4992_);
    return v___x_4993_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___boxed(
    mut v_00_u03b2_4994_: *mut crate::leanh::LeanObject,
    mut v_keys_4995_: *mut crate::leanh::LeanObject,
    mut v_vals_4996_: *mut crate::leanh::LeanObject,
    mut v_heq_4997_: *mut crate::leanh::LeanObject,
    mut v_i_4998_: *mut crate::leanh::LeanObject,
    mut v_k_4999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5000_: u8 = 0;
    let mut v_r_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5000_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(v_00_u03b2_4994_, v_keys_4995_, v_vals_4996_, v_heq_4997_, v_i_4998_, v_k_4999_);
    crate::leanh::lean_dec_ref(v_k_4999_);
    crate::leanh::lean_dec_ref(v_vals_4996_);
    crate::leanh::lean_dec_ref(v_keys_4995_);
    v_r_5001_ = crate::leanh::lean_box((v_res_5000_) as usize);
    return v_r_5001_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(
    mut v_as_5002_: *mut crate::leanh::LeanObject,
    mut v_sz_5003_: usize,
    mut v_i_5004_: usize,
    mut v_b_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: usize = 0;
    let mut v___x_5014_: usize = 0;
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: u8 = 0;
    let mut v___x_5025_: u8 = 0;
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5032_: u8 = 0;
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_a_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5016_ = lean_usize_dec_lt(v_i_5004_, v_sz_5003_);
                if v___x_5016_ == 0 {
                    v___x_5017_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5017_, 0, v_b_5005_);
                    return v___x_5017_;
                } else {
                    v_a_5018_ = lean_array_uget_borrowed(v_as_5002_, v_i_5004_);
                    crate::leanh::lean_inc(v_a_5018_);
                    v___x_5019_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(
                        v_a_5018_,
                        v___y_5008_,
                        v___y_5009_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5019_) == 0 {
                        v_toSignature_5020_ = crate::leanh::lean_ctor_get(v_a_5018_, 0);
                        v_a_5021_ = crate::leanh::lean_ctor_get(v___x_5019_, 0);
                        crate::leanh::lean_inc(v_a_5021_);
                        crate::leanh::lean_dec_ref_known(v___x_5019_, 1);
                        v_name_5022_ = crate::leanh::lean_ctor_get(v_toSignature_5020_, 0);
                        v___x_5023_ = crate::leanh::lean_box(0);
                        v___x_5024_ = l_Lean_isPrivateName(v_name_5022_);
                        if v___x_5024_ == 0 {
                            v___x_5025_ = (crate::leanh::lean_unbox(v_a_5021_) as u8);
                            crate::leanh::lean_dec(v_a_5021_);
                            if v___x_5025_ == 0 {
                                v_a_5012_ = v___x_5023_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5026_ = lean_st_ref_get(v___y_5009_);
                                crate::leanh::lean_dec(v___x_5026_);
                                v___x_5027_ = l_Lean_NameSet_empty;
                                crate::leanh::lean_inc_n(v_a_5018_, 2);
                                v___x_5028_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_a_5018_, v_a_5018_, v___x_5027_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
                                if crate::leanh::lean_obj_tag(v___x_5028_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5028_, 1);
                                    v_a_5012_ = v___x_5023_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_5029_ = crate::leanh::lean_ctor_get(v___x_5028_, 0);
                                    v_isSharedCheck_5036_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5028_)) as u8;
                                    if v_isSharedCheck_5036_ == 0 {
                                        v___x_5031_ = v___x_5028_;
                                        v_isShared_5032_ = v_isSharedCheck_5036_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5029_);
                                        crate::leanh::lean_dec(v___x_5028_);
                                        v___x_5031_ = crate::leanh::lean_box(0);
                                        v_isShared_5032_ = v_isSharedCheck_5036_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5021_);
                            v_a_5012_ = v___x_5023_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5037_ = crate::leanh::lean_ctor_get(v___x_5019_, 0);
                        v_isSharedCheck_5044_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5019_)) as u8;
                        if v_isSharedCheck_5044_ == 0 {
                            v___x_5039_ = v___x_5019_;
                            v_isShared_5040_ = v_isSharedCheck_5044_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5037_);
                            crate::leanh::lean_dec(v___x_5019_);
                            v___x_5039_ = crate::leanh::lean_box(0);
                            v_isShared_5040_ = v_isSharedCheck_5044_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5013_ = 1usize;
                v___x_5014_ = lean_usize_add(v_i_5004_, v___x_5013_);
                v_i_5004_ = v___x_5014_;
                v_b_5005_ = v_a_5012_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5032_ == 0 {
                    v___x_5034_ = v___x_5031_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
                    v___x_5034_ = v_reuseFailAlloc_5035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5034_;
            }
            4 => {
                if v_isShared_5040_ == 0 {
                    v___x_5042_ = v___x_5039_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
                    v___x_5042_ = v_reuseFailAlloc_5043_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0___boxed(
    mut v_as_5045_: *mut crate::leanh::LeanObject,
    mut v_sz_5046_: *mut crate::leanh::LeanObject,
    mut v_i_5047_: *mut crate::leanh::LeanObject,
    mut v_b_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5054_: usize = 0;
    let mut v_i_boxed_5055_: usize = 0;
    let mut v_res_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5054_ = crate::leanh::lean_unbox_usize(v_sz_5046_);
    crate::leanh::lean_dec(v_sz_5046_);
    v_i_boxed_5055_ = crate::leanh::lean_unbox_usize(v_i_5047_);
    crate::leanh::lean_dec(v_i_5047_);
    v_res_5056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_as_5045_, v_sz_boxed_5054_, v_i_boxed_5055_, v_b_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
    crate::leanh::lean_dec(v___y_5052_);
    crate::leanh::lean_dec_ref(v___y_5051_);
    crate::leanh::lean_dec(v___y_5050_);
    crate::leanh::lean_dec_ref(v___y_5049_);
    crate::leanh::lean_dec_ref(v_as_5045_);
    return v_res_5056_;
}
pub unsafe fn l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(
    mut v_decls_5057_: *mut crate::leanh::LeanObject,
    mut v___y_5058_: *mut crate::leanh::LeanObject,
    mut v___y_5059_: *mut crate::leanh::LeanObject,
    mut v___y_5060_: *mut crate::leanh::LeanObject,
    mut v___y_5061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_5066_: u8 = 0;
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5069_: usize = 0;
    let mut v___x_5070_: usize = 0;
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5074_: u8 = 0;
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5078_: u8 = 0;
    let mut v_unused_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5063_ = lean_st_ref_get(v___y_5061_);
                v_env_5064_ = crate::leanh::lean_ctor_get(v___x_5063_, 0);
                crate::leanh::lean_inc_ref(v_env_5064_);
                crate::leanh::lean_dec(v___x_5063_);
                v___x_5065_ = l_Lean_Environment_header(v_env_5064_);
                crate::leanh::lean_dec_ref(v_env_5064_);
                v_isModule_5066_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5065_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
                );
                crate::leanh::lean_dec_ref(v___x_5065_);
                if v_isModule_5066_ == 0 {
                    v___x_5067_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5067_, 0, v_decls_5057_);
                    return v___x_5067_;
                } else {
                    v___x_5068_ = crate::leanh::lean_box(0);
                    v_sz_5069_ = lean_array_size(v_decls_5057_);
                    v___x_5070_ = 0usize;
                    v___x_5071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_decls_5057_, v_sz_5069_, v___x_5070_, v___x_5068_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
                    if crate::leanh::lean_obj_tag(v___x_5071_) == 0 {
                        v_isSharedCheck_5078_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5071_)) as u8;
                        if v_isSharedCheck_5078_ == 0 {
                            v_unused_5079_ = crate::leanh::lean_ctor_get(v___x_5071_, 0);
                            crate::leanh::lean_dec(v_unused_5079_);
                            v___x_5073_ = v___x_5071_;
                            v_isShared_5074_ = v_isSharedCheck_5078_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5071_);
                            v___x_5073_ = crate::leanh::lean_box(0);
                            v_isShared_5074_ = v_isSharedCheck_5078_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_decls_5057_);
                        v_a_5080_ = crate::leanh::lean_ctor_get(v___x_5071_, 0);
                        v_isSharedCheck_5087_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5071_)) as u8;
                        if v_isSharedCheck_5087_ == 0 {
                            v___x_5082_ = v___x_5071_;
                            v_isShared_5083_ = v_isSharedCheck_5087_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5080_);
                            crate::leanh::lean_dec(v___x_5071_);
                            v___x_5082_ = crate::leanh::lean_box(0);
                            v_isShared_5083_ = v_isSharedCheck_5087_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5074_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5073_, 0, v_decls_5057_);
                    v___x_5076_ = v___x_5073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_decls_5057_);
                    v___x_5076_ = v_reuseFailAlloc_5077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5076_;
            }
            3 => {
                if v_isShared_5083_ == 0 {
                    v___x_5085_ = v___x_5082_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5086_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
                    v___x_5085_ = v_reuseFailAlloc_5086_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed(
    mut v_decls_5088_: *mut crate::leanh::LeanObject,
    mut v___y_5089_: *mut crate::leanh::LeanObject,
    mut v___y_5090_: *mut crate::leanh::LeanObject,
    mut v___y_5091_: *mut crate::leanh::LeanObject,
    mut v___y_5092_: *mut crate::leanh::LeanObject,
    mut v___y_5093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5094_ = l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(
        v_decls_5088_,
        v___y_5089_,
        v___y_5090_,
        v___y_5091_,
        v___y_5092_,
    );
    crate::leanh::lean_dec(v___y_5092_);
    crate::leanh::lean_dec_ref(v___y_5091_);
    crate::leanh::lean_dec(v___y_5090_);
    crate::leanh::lean_dec_ref(v___y_5089_);
    return v_res_5094_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0;
    v___x_5108_ = l_Lean_stringToMessageData(v___x_5107_);
    return v___x_5108_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(
    mut v_phase_5109_: u8,
    mut v___x_5110_: u8,
    mut v_as_5111_: *mut crate::leanh::LeanObject,
    mut v_sz_5112_: usize,
    mut v_i_5113_: usize,
    mut v_b_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
    mut v___y_5117_: *mut crate::leanh::LeanObject,
    mut v___y_5118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: usize = 0;
    let mut v___x_5123_: usize = 0;
    let mut v___x_5125_: u8 = 0;
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: u8 = 0;
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: u8 = 0;
    let mut v_options_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5143_: u8 = 0;
    let mut v_inheritedTraceOptions_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: u8 = 0;
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5125_ = lean_usize_dec_lt(v_i_5113_, v_sz_5112_);
                if v___x_5125_ == 0 {
                    v___x_5126_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5126_, 0, v_b_5114_);
                    return v___x_5126_;
                } else {
                    v___x_5127_ = lean_st_ref_get(v___y_5118_);
                    v_env_5128_ = crate::leanh::lean_ctor_get(v___x_5127_, 0);
                    crate::leanh::lean_inc_ref(v_env_5128_);
                    crate::leanh::lean_dec(v___x_5127_);
                    v_a_5129_ = lean_array_uget_borrowed(v_as_5111_, v_i_5113_);
                    v_toSignature_5130_ = crate::leanh::lean_ctor_get(v_a_5129_, 0);
                    v_name_5131_ = crate::leanh::lean_ctor_get(v_toSignature_5130_, 0);
                    v___x_5132_ = crate::leanh::lean_box(0);
                    v___x_5140_ = l_Lean_Environment_setExporting(v_env_5128_, v___x_5110_);
                    crate::leanh::lean_inc(v_name_5131_);
                    v___x_5141_ =
                        l_Lean_Environment_contains(v___x_5140_, v_name_5131_, v___x_5110_);
                    if v___x_5141_ == 0 {
                        v_a_5121_ = v___x_5132_;
                        state = 1;
                        continue;
                    } else {
                        v_options_5142_ = crate::leanh::lean_ctor_get(v___y_5117_, 2);
                        v_hasTrace_5143_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_5142_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_5143_ == 0 {
                            v___y_5134_ = v___y_5115_;
                            v___y_5135_ = v___y_5116_;
                            v___y_5136_ = v___y_5117_;
                            v___y_5137_ = v___y_5118_;
                            state = 2;
                            continue;
                        } else {
                            v_inheritedTraceOptions_5144_ =
                                crate::leanh::lean_ctor_get(v___y_5117_, 13);
                            v___x_5145_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2;
                            v___x_5146_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
                            v___x_5147_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_5144_,
                                v_options_5142_,
                                v___x_5146_,
                            );
                            if v___x_5147_ == 0 {
                                v___y_5134_ = v___y_5115_;
                                v___y_5135_ = v___y_5116_;
                                v___y_5136_ = v___y_5117_;
                                v___y_5137_ = v___y_5118_;
                                state = 2;
                                continue;
                            } else {
                                v___x_5148_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
                                crate::leanh::lean_inc(v_name_5131_);
                                v___x_5149_ = l_Lean_MessageData_ofName(v_name_5131_);
                                v___x_5150_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5150_, 0, v___x_5148_);
                                crate::leanh::lean_ctor_set(v___x_5150_, 1, v___x_5149_);
                                v___x_5151_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1);
                                v___x_5152_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5152_, 0, v___x_5150_);
                                crate::leanh::lean_ctor_set(v___x_5152_, 1, v___x_5151_);
                                v___x_5153_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_5145_, v___x_5152_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_);
                                if crate::leanh::lean_obj_tag(v___x_5153_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5153_, 1);
                                    v___y_5134_ = v___y_5115_;
                                    v___y_5135_ = v___y_5116_;
                                    v___y_5136_ = v___y_5117_;
                                    v___y_5137_ = v___y_5118_;
                                    state = 2;
                                    continue;
                                } else {
                                    return v___x_5153_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5122_ = 1usize;
                v___x_5123_ = lean_usize_add(v_i_5113_, v___x_5122_);
                v_i_5113_ = v___x_5123_;
                v_b_5114_ = v_a_5121_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5138_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_5109_);
                crate::leanh::lean_inc(v_a_5129_);
                v___x_5139_ = l_Lean_Compiler_LCNF_markDeclPublicRec(
                    v___x_5138_,
                    v_phase_5109_,
                    v_a_5129_,
                    v___y_5134_,
                    v___y_5135_,
                    v___y_5136_,
                    v___y_5137_,
                );
                if crate::leanh::lean_obj_tag(v___x_5139_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5139_, 1);
                    v_a_5121_ = v___x_5132_;
                    state = 1;
                    continue;
                } else {
                    return v___x_5139_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___boxed(
    mut v_phase_5154_: *mut crate::leanh::LeanObject,
    mut v___x_5155_: *mut crate::leanh::LeanObject,
    mut v_as_5156_: *mut crate::leanh::LeanObject,
    mut v_sz_5157_: *mut crate::leanh::LeanObject,
    mut v_i_5158_: *mut crate::leanh::LeanObject,
    mut v_b_5159_: *mut crate::leanh::LeanObject,
    mut v___y_5160_: *mut crate::leanh::LeanObject,
    mut v___y_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
    mut v___y_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_5165_: u8 = 0;
    let mut v___x_2836__boxed_5166_: u8 = 0;
    let mut v_sz_boxed_5167_: usize = 0;
    let mut v_i_boxed_5168_: usize = 0;
    let mut v_res_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_5165_ = (crate::leanh::lean_unbox(v_phase_5154_) as u8);
    v___x_2836__boxed_5166_ = (crate::leanh::lean_unbox(v___x_5155_) as u8);
    v_sz_boxed_5167_ = crate::leanh::lean_unbox_usize(v_sz_5157_);
    crate::leanh::lean_dec(v_sz_5157_);
    v_i_boxed_5168_ = crate::leanh::lean_unbox_usize(v_i_5158_);
    crate::leanh::lean_dec(v_i_5158_);
    v_res_5169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_boxed_5165_, v___x_2836__boxed_5166_, v_as_5156_, v_sz_boxed_5167_, v_i_boxed_5168_, v_b_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_);
    crate::leanh::lean_dec(v___y_5163_);
    crate::leanh::lean_dec_ref(v___y_5162_);
    crate::leanh::lean_dec(v___y_5161_);
    crate::leanh::lean_dec_ref(v___y_5160_);
    crate::leanh::lean_dec_ref(v_as_5156_);
    return v_res_5169_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inferVisibility___lam__0(
    mut v_phase_5170_: u8,
    mut v_decls_5171_: *mut crate::leanh::LeanObject,
    mut v___y_5172_: *mut crate::leanh::LeanObject,
    mut v___y_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
    mut v___y_5175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_5180_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5183_: usize = 0;
    let mut v___x_5184_: usize = 0;
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5188_: u8 = 0;
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5192_: u8 = 0;
    let mut v_unused_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5197_: u8 = 0;
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5177_ = lean_st_ref_get(v___y_5175_);
                v_env_5178_ = crate::leanh::lean_ctor_get(v___x_5177_, 0);
                crate::leanh::lean_inc_ref(v_env_5178_);
                crate::leanh::lean_dec(v___x_5177_);
                v___x_5179_ = l_Lean_Environment_header(v_env_5178_);
                crate::leanh::lean_dec_ref(v_env_5178_);
                v_isModule_5180_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5179_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
                );
                crate::leanh::lean_dec_ref(v___x_5179_);
                if v_isModule_5180_ == 0 {
                    v___x_5181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5181_, 0, v_decls_5171_);
                    return v___x_5181_;
                } else {
                    v___x_5182_ = crate::leanh::lean_box(0);
                    v_sz_5183_ = lean_array_size(v_decls_5171_);
                    v___x_5184_ = 0usize;
                    v___x_5185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_5170_, v_isModule_5180_, v_decls_5171_, v_sz_5183_, v___x_5184_, v___x_5182_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
                    if crate::leanh::lean_obj_tag(v___x_5185_) == 0 {
                        v_isSharedCheck_5192_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5185_)) as u8;
                        if v_isSharedCheck_5192_ == 0 {
                            v_unused_5193_ = crate::leanh::lean_ctor_get(v___x_5185_, 0);
                            crate::leanh::lean_dec(v_unused_5193_);
                            v___x_5187_ = v___x_5185_;
                            v_isShared_5188_ = v_isSharedCheck_5192_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5185_);
                            v___x_5187_ = crate::leanh::lean_box(0);
                            v_isShared_5188_ = v_isSharedCheck_5192_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_decls_5171_);
                        v_a_5194_ = crate::leanh::lean_ctor_get(v___x_5185_, 0);
                        v_isSharedCheck_5201_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5185_)) as u8;
                        if v_isSharedCheck_5201_ == 0 {
                            v___x_5196_ = v___x_5185_;
                            v_isShared_5197_ = v_isSharedCheck_5201_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5194_);
                            crate::leanh::lean_dec(v___x_5185_);
                            v___x_5196_ = crate::leanh::lean_box(0);
                            v_isShared_5197_ = v_isSharedCheck_5201_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5187_, 0, v_decls_5171_);
                    v___x_5190_ = v___x_5187_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5191_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_decls_5171_);
                    v___x_5190_ = v_reuseFailAlloc_5191_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5190_;
            }
            3 => {
                if v_isShared_5197_ == 0 {
                    v___x_5199_ = v___x_5196_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5200_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
                    v___x_5199_ = v_reuseFailAlloc_5200_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed(
    mut v_phase_5202_: *mut crate::leanh::LeanObject,
    mut v_decls_5203_: *mut crate::leanh::LeanObject,
    mut v___y_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_5209_: u8 = 0;
    let mut v_res_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_5209_ = (crate::leanh::lean_unbox(v_phase_5202_) as u8);
    v_res_5210_ = l_Lean_Compiler_LCNF_inferVisibility___lam__0(
        v_phase_boxed_5209_,
        v_decls_5203_,
        v___y_5204_,
        v___y_5205_,
        v___y_5206_,
        v___y_5207_,
    );
    crate::leanh::lean_dec(v___y_5207_);
    crate::leanh::lean_dec_ref(v___y_5206_);
    crate::leanh::lean_dec(v___y_5205_);
    crate::leanh::lean_dec_ref(v___y_5204_);
    return v_res_5210_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inferVisibility(
    mut v_phase_5213_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: u8 = 0;
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5214_ = crate::leanh::lean_box((v_phase_5213_) as usize);
    v___f_5215_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5215_, 0, v___x_5214_);
    v___x_5216_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5217_ = 0;
    v___x_5218_ = l_Lean_Compiler_LCNF_inferVisibility___closed__0;
    v___x_5219_ = crate::leanh::lean_alloc_ctor(0, 3, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_5219_, 0, v___x_5216_);
    crate::leanh::lean_ctor_set(v___x_5219_, 1, v___x_5218_);
    crate::leanh::lean_ctor_set(v___x_5219_, 2, v___f_5215_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5219_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_phase_5213_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5219_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v_phase_5213_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5219_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
        v___x_5217_,
    );
    return v___x_5219_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inferVisibility___boxed(
    mut v_phase_5220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_5221_: u8 = 0;
    let mut v_res_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_5221_ = (crate::leanh::lean_unbox(v_phase_5220_) as u8);
    v_res_5222_ = l_Lean_Compiler_LCNF_inferVisibility(v_phase_boxed_5221_);
    return v_res_5222_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5274_ = crate::leanh::lean_unsigned_to_nat(3356661454);
    v___x_5275_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_;
    v___x_5276_ = l_Lean_Name_num___override(v___x_5275_, v___x_5274_);
    return v___x_5276_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5278_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_;
    v___x_5279_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
    v___x_5280_ = l_Lean_Name_str___override(v___x_5279_, v___x_5278_);
    return v___x_5280_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5282_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_;
    v___x_5283_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
    v___x_5284_ = l_Lean_Name_str___override(v___x_5283_, v___x_5282_);
    return v___x_5284_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5285_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_5286_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
    v___x_5287_ = l_Lean_Name_num___override(v___x_5286_, v___x_5285_);
    return v___x_5287_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: u8 = 0;
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5289_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2;
    v___x_5290_ = 0;
    v___x_5291_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
    v___x_5292_ = l_Lean_registerTraceClass(v___x_5289_, v___x_5290_, v___x_5291_);
    return v___x_5292_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2____boxed(
    mut v_a_5293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5294_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
    return v_res_5294_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Visibility(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Visibility(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Visibility(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Visibility(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Visibility(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Visibility(builtin);
}

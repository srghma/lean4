// Lean compiler output
// Module: Lean.Compiler.LCNF.Visibility
// Imports: Lean.Compiler.ImplementedByAttr Lean.ExtraModUses Lean.Compiler.Options Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.PassManager
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [105, 110, 102, 101, 114, 86, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value) as *mut LeanObject;
static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value) as *mut LeanObject,12284906337363465325 as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__3_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [77, 97, 114, 107, 105, 110, 103, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_value: LeanStringObject<65> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 65,
        m_capacity: 65,
        m_length: 64,
        m_data: [
            32, 97, 115, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 116, 32, 98, 101, 99,
            97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 111, 112, 97, 113, 117, 101, 32, 97,
            110, 100, 32, 105, 116, 115, 32, 98, 111, 100, 121, 32, 108, 111, 111, 107, 115, 32,
            114, 101, 108, 101, 118, 97, 110, 116, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [32, 97, 115, 32, 111, 112, 97, 113, 117, 101, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 117, 115, 101, 100, 32, 98, 121, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 116, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [96, 44, 32, 109, 97, 121, 32, 110, 111, 116, 32, 97, 99, 99, 101, 115, 115, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [96, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 96, 109, 101, 116, 97, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6_value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [96, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 97, 115, 32, 96, 109, 101, 116, 97, 96, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 96, 109, 101, 116, 97, 96, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [96, 44, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14_value: LeanStringObject<63> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 32, 104, 101, 114, 101, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 109, 101, 116, 97, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 110, 111, 116, 32, 109, 97, 114, 107, 101, 100, 32, 96, 109, 101, 116, 97, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 112, 117, 98, 108, 105, 99, 32, 96, 109, 101, 116, 97, 96, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20_value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 32, 104, 101, 114, 101, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__3_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__18_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1_value: LeanStringObject<49> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [67, 97, 110, 110, 111, 116, 32, 99, 111, 109, 112, 105, 108, 101, 32, 105, 110, 108, 105, 110, 101, 47, 115, 112, 101, 99, 105, 97, 108, 105, 122, 105, 110, 103, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [96, 32, 97, 115, 32, 105, 116, 32, 117, 115, 101, 115, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [96, 32, 111, 102, 32, 109, 111, 100, 117, 108, 101, 32, 96, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7_value: LeanStringObject<80> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 80, m_capacity: 80, m_length: 79, m_data: [96, 32, 119, 104, 105, 99, 104, 32, 109, 117, 115, 116, 32, 98, 101, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 117, 98, 108, 105, 99, 108, 121, 46, 32, 84, 104, 105, 115, 32, 108, 105, 109, 105, 116, 97, 116, 105, 111, 110, 32, 109, 97, 121, 32, 98, 101, 32, 108, 105, 102, 116, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 102, 117, 116, 117, 114, 101, 46, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1_value: LeanStringObject<24> =
    LeanStringObject {
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
            99, 104, 101, 99, 107, 84, 101, 109, 112, 108, 97, 116, 101, 86, 105, 115, 105, 98,
            105, 108, 105, 116, 121, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__1_value)
                as *mut LeanObject,
            15185984258296179725 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_checkTemplateVisibility: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_checkTemplateVisibility___closed__3_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [32, 97, 115, 32, 111, 112, 97, 113, 117, 101, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 97, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 102, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_inferVisibility___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__1_value) as *mut LeanObject,3059348757014389675 as *mut LeanObject] };
static mut l_Lean_Compiler_LCNF_inferVisibility___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_inferVisibility___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [86, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,7864849472683266603 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,270195162246034326 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,11649833169365808703 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value) as *mut LeanObject,10150642787462906833 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,15828838177423456980 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,14679371497876971281 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,9775471812865212668 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,15772378170105911453 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__0_value) as *mut LeanObject,9088531055874635291 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,4427328837111778918 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject,15667018320580198296 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(
    mut v_e_2648_: *mut LeanObject,
    mut v_s_2649_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_e_2648_) {
        3 => {
            let mut v_declName_2650_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
            v_declName_2650_ = lean_ctor_get(v_e_2648_, 0);
            lean_inc(v_declName_2650_);
            lean_dec_ref_known(v_e_2648_, 3);
            v___x_2651_ = l_Lean_NameSet_insert(v_s_2649_, v_declName_2650_);
            return v___x_2651_;
        }
        9 => {
            let mut v_fn_2652_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
            v_fn_2652_ = lean_ctor_get(v_e_2648_, 0);
            lean_inc(v_fn_2652_);
            lean_dec_ref_known(v_e_2648_, 2);
            v___x_2653_ = l_Lean_NameSet_insert(v_s_2649_, v_fn_2652_);
            return v___x_2653_;
        }
        10 => {
            let mut v_fn_2654_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
            v_fn_2654_ = lean_ctor_get(v_e_2648_, 0);
            lean_inc(v_fn_2654_);
            lean_dec_ref_known(v_e_2648_, 2);
            v___x_2655_ = l_Lean_NameSet_insert(v_s_2649_, v_fn_2654_);
            return v___x_2655_;
        }
        _ => {
            lean_dec(v_e_2648_);
            return v_s_2649_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue(
    mut v_pu_2656_: u8,
    mut v_e_2657_: *mut LeanObject,
    mut v_s_2658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    v___x_2659_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(v_e_2657_, v_s_2658_);
    return v___x_2659_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___boxed(
    mut v_pu_2660_: *mut LeanObject,
    mut v_e_2661_: *mut LeanObject,
    mut v_s_2662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2663_: u8 = 0;
    let mut v_res_2664_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2663_ = (lean_unbox(v_pu_2660_) as u8);
    v_res_2664_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue(v_pu_boxed_2663_, v_e_2661_, v_s_2662_);
    return v_res_2664_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(
    mut v_pu_2665_: u8,
    mut v_code_2666_: *mut LeanObject,
    mut v_s_2667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: usize = 0;
    let mut v___x_2690_: usize = 0;
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: usize = 0;
    let mut v___x_2693_: usize = 0;
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_2666_) {
                0 => {
                    v_decl_2668_ = lean_ctor_get(v_code_2666_, 0);
                    lean_inc_ref(v_decl_2668_);
                    v_k_2669_ = lean_ctor_get(v_code_2666_, 1);
                    lean_inc_ref(v_k_2669_);
                    lean_dec_ref_known(v_code_2666_, 2);
                    v_value_2670_ = lean_ctor_get(v_decl_2668_, 3);
                    lean_inc(v_value_2670_);
                    lean_dec_ref(v_decl_2668_);
                    v___x_2671_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_collectLetValue___redArg(v_value_2670_, v_s_2667_);
                    v_code_2666_ = v_k_2669_;
                    v_s_2667_ = v___x_2671_;
                    state = 0;
                    continue;
                }
                2 => {
                    v_decl_2673_ = lean_ctor_get(v_code_2666_, 0);
                    lean_inc_ref(v_decl_2673_);
                    v_k_2674_ = lean_ctor_get(v_code_2666_, 1);
                    lean_inc_ref(v_k_2674_);
                    lean_dec_ref_known(v_code_2666_, 2);
                    v_value_2675_ = lean_ctor_get(v_decl_2673_, 4);
                    lean_inc_ref(v_value_2675_);
                    lean_dec_ref(v_decl_2673_);
                    v___x_2676_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_2665_, v_k_2674_, v_s_2667_);
                    v_code_2666_ = v_value_2675_;
                    v_s_2667_ = v___x_2676_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_2678_ = lean_ctor_get(v_code_2666_, 0);
                    lean_inc_ref(v_decl_2678_);
                    v_k_2679_ = lean_ctor_get(v_code_2666_, 1);
                    lean_inc_ref(v_k_2679_);
                    lean_dec_ref_known(v_code_2666_, 2);
                    v_value_2680_ = lean_ctor_get(v_decl_2678_, 4);
                    lean_inc_ref(v_value_2680_);
                    lean_dec_ref(v_decl_2678_);
                    v___x_2681_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_2665_, v_k_2679_, v_s_2667_);
                    v_code_2666_ = v_value_2680_;
                    v_s_2667_ = v___x_2681_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_cases_2683_ = lean_ctor_get(v_code_2666_, 0);
                    lean_inc_ref(v_cases_2683_);
                    lean_dec_ref_known(v_code_2666_, 1);
                    v_alts_2684_ = lean_ctor_get(v_cases_2683_, 3);
                    lean_inc_ref(v_alts_2684_);
                    lean_dec_ref(v_cases_2683_);
                    v___x_2685_ = lean_unsigned_to_nat(0);
                    v___x_2686_ = lean_array_get_size(v_alts_2684_);
                    v___x_2687_ = lean_nat_dec_lt(v___x_2685_, v___x_2686_);
                    if v___x_2687_ == 0 {
                        lean_dec_ref(v_alts_2684_);
                        return v_s_2667_;
                    } else {
                        v___x_2688_ = lean_nat_dec_le(v___x_2686_, v___x_2686_);
                        if v___x_2688_ == 0 {
                            if v___x_2687_ == 0 {
                                lean_dec_ref(v_alts_2684_);
                                return v_s_2667_;
                            } else {
                                v___x_2689_ = 0usize;
                                v___x_2690_ = lean_usize_of_nat(v___x_2686_);
                                v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_2665_, v_alts_2684_, v___x_2689_, v___x_2690_, v_s_2667_);
                                lean_dec_ref(v_alts_2684_);
                                return v___x_2691_;
                            }
                        } else {
                            v___x_2692_ = 0usize;
                            v___x_2693_ = lean_usize_of_nat(v___x_2686_);
                            v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_2665_, v_alts_2684_, v___x_2692_, v___x_2693_, v_s_2667_);
                            lean_dec_ref(v_alts_2684_);
                            return v___x_2694_;
                        }
                    }
                }
                _ => {
                    lean_dec_ref(v_code_2666_);
                    return v_s_2667_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(
    mut v_pu_2695_: u8,
    mut v_as_2696_: *mut LeanObject,
    mut v_i_2697_: usize,
    mut v_stop_2698_: usize,
    mut v_b_2699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: usize = 0;
    let mut v___x_2703_: usize = 0;
    let mut v___x_2705_: u8 = 0;
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2705_ = lean_usize_dec_eq(v_i_2697_, v_stop_2698_);
                if v___x_2705_ == 0 {
                    v___x_2706_ = lean_array_uget_borrowed(v_as_2696_, v_i_2697_);
                    match lean_obj_tag(v___x_2706_) {
                        0 => {
                            v_code_2707_ = lean_ctor_get(v___x_2706_, 2);
                            lean_inc_ref(v_code_2707_);
                            v___x_2708_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_2695_, v_code_2707_, v_b_2699_);
                            v___y_2701_ = v___x_2708_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_2709_ = lean_ctor_get(v___x_2706_, 1);
                            lean_inc_ref(v_code_2709_);
                            v___x_2710_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_2695_, v_code_2709_, v_b_2699_);
                            v___y_2701_ = v___x_2710_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_2711_ = lean_ctor_get(v___x_2706_, 0);
                            lean_inc_ref(v_code_2711_);
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
    mut v_pu_2713_: *mut LeanObject,
    mut v_as_2714_: *mut LeanObject,
    mut v_i_2715_: *mut LeanObject,
    mut v_stop_2716_: *mut LeanObject,
    mut v_b_2717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2718_: u8 = 0;
    let mut v_i_boxed_2719_: usize = 0;
    let mut v_stop_boxed_2720_: usize = 0;
    let mut v_res_2721_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2718_ = (lean_unbox(v_pu_2713_) as u8);
    v_i_boxed_2719_ = lean_unbox_usize(v_i_2715_);
    lean_dec(v_i_2715_);
    v_stop_boxed_2720_ = lean_unbox_usize(v_stop_2716_);
    lean_dec(v_stop_2716_);
    v_res_2721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls_spec__0(v_pu_boxed_2718_, v_as_2714_, v_i_boxed_2719_, v_stop_boxed_2720_, v_b_2717_);
    lean_dec_ref(v_as_2714_);
    return v_res_2721_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls___boxed(
    mut v_pu_2722_: *mut LeanObject,
    mut v_code_2723_: *mut LeanObject,
    mut v_s_2724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2725_: u8 = 0;
    let mut v_res_2726_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2725_ = (lean_unbox(v_pu_2722_) as u8);
    v_res_2726_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(
        v_pu_boxed_2725_,
        v_code_2723_,
        v_s_2724_,
    );
    return v_res_2726_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(
    mut v_opts_2727_: *mut LeanObject,
    mut v_opt_2728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    v_name_2729_ = lean_ctor_get(v_opt_2728_, 0);
    v_defValue_2730_ = lean_ctor_get(v_opt_2728_, 1);
    v_map_2731_ = lean_ctor_get(v_opts_2727_, 0);
    v___x_2732_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2731_,
            v_name_2729_,
        );
    if lean_obj_tag(v___x_2732_) == 0 {
        lean_inc(v_defValue_2730_);
        return v_defValue_2730_;
    } else {
        let mut v_val_2733_: *mut LeanObject = core::ptr::null_mut();
        v_val_2733_ = lean_ctor_get(v___x_2732_, 0);
        lean_inc(v_val_2733_);
        lean_dec_ref_known(v___x_2732_, 1);
        if lean_obj_tag(v_val_2733_) == 3 {
            let mut v_v_2734_: *mut LeanObject = core::ptr::null_mut();
            v_v_2734_ = lean_ctor_get(v_val_2733_, 0);
            lean_inc(v_v_2734_);
            lean_dec_ref_known(v_val_2733_, 1);
            return v_v_2734_;
        } else {
            lean_dec(v_val_2733_);
            lean_inc(v_defValue_2730_);
            return v_defValue_2730_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0___boxed(
    mut v_opts_2735_: *mut LeanObject,
    mut v_opt_2736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2737_: *mut LeanObject = core::ptr::null_mut();
    v_res_2737_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v_opts_2735_, v_opt_2736_);
    lean_dec_ref(v_opt_2736_);
    lean_dec_ref(v_opts_2735_);
    return v_res_2737_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(
    mut v_v_2738_: *mut LeanObject,
    mut v_f_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2749_: u8 = 0;
    let mut v___x_2750_: u8 = 0;
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2755_: u8 = 0;
    let mut v_unused_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2738_) == 0 {
                    v_code_2745_ = lean_ctor_get(v_v_2738_, 0);
                    lean_inc_ref(v_code_2745_);
                    lean_dec_ref_known(v_v_2738_, 1);
                    lean_inc(v___y_2743_);
                    lean_inc_ref(v___y_2742_);
                    lean_inc(v___y_2741_);
                    lean_inc_ref(v___y_2740_);
                    v___x_2746_ = lean_apply_6(
                        v_f_2739_,
                        v_code_2745_,
                        v___y_2740_,
                        v___y_2741_,
                        v___y_2742_,
                        v___y_2743_,
                        lean_box(0),
                    );
                    return v___x_2746_;
                } else {
                    lean_dec_ref(v_f_2739_);
                    v_isSharedCheck_2755_ = (!lean_is_exclusive(v_v_2738_)) as u8;
                    if v_isSharedCheck_2755_ == 0 {
                        v_unused_2756_ = lean_ctor_get(v_v_2738_, 0);
                        lean_dec(v_unused_2756_);
                        v___x_2748_ = v_v_2738_;
                        v_isShared_2749_ = v_isSharedCheck_2755_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_v_2738_);
                        v___x_2748_ = lean_box(0);
                        v_isShared_2749_ = v_isSharedCheck_2755_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2750_ = 0;
                v___x_2751_ = lean_box((v___x_2750_) as usize);
                if v_isShared_2749_ == 0 {
                    lean_ctor_set_tag(v___x_2748_, 0);
                    lean_ctor_set(v___x_2748_, 0, v___x_2751_);
                    v___x_2753_ = v___x_2748_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
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
    mut v_v_2757_: *mut LeanObject,
    mut v_f_2758_: *mut LeanObject,
    mut v___y_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
    mut v___y_2761_: *mut LeanObject,
    mut v___y_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2764_: *mut LeanObject = core::ptr::null_mut();
    v_res_2764_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_2757_, v_f_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
    lean_dec(v___y_2762_);
    lean_dec_ref(v___y_2761_);
    lean_dec(v___y_2760_);
    lean_dec_ref(v___y_2759_);
    return v_res_2764_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(
    mut v_pu_2765_: u8,
    mut v_v_2766_: *mut LeanObject,
    mut v_f_2767_: *mut LeanObject,
    mut v___y_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
    mut v___y_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    v___x_2773_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_v_2766_, v_f_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
    return v___x_2773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___boxed(
    mut v_pu_2774_: *mut LeanObject,
    mut v_v_2775_: *mut LeanObject,
    mut v_f_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
    mut v___y_2778_: *mut LeanObject,
    mut v___y_2779_: *mut LeanObject,
    mut v___y_2780_: *mut LeanObject,
    mut v___y_2781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2782_: u8 = 0;
    let mut v_res_2783_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2782_ = (lean_unbox(v_pu_2774_) as u8);
    v_res_2783_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1(v_pu_boxed_2782_, v_v_2775_, v_f_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
    lean_dec(v___y_2780_);
    lean_dec_ref(v___y_2779_);
    lean_dec(v___y_2778_);
    lean_dec_ref(v___y_2777_);
    return v_res_2783_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0(
    mut v_toSignature_2784_: *mut LeanObject,
    mut v_a_2785_: u8,
    mut v_pu_2786_: u8,
    mut v_code_2787_: *mut LeanObject,
    mut v___y_2788_: *mut LeanObject,
    mut v___y_2789_: *mut LeanObject,
    mut v___y_2790_: *mut LeanObject,
    mut v___y_2791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2804_: u8 = 0;
    let mut v_kind_2805_: u8 = 0;
    let mut v___x_2806_: u8 = 0;
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2793_ = lean_st_ref_get(v___y_2791_);
                v_env_2794_ = lean_ctor_get(v___x_2793_, 0);
                lean_inc_ref(v_env_2794_);
                lean_dec(v___x_2793_);
                v_name_2795_ = lean_ctor_get(v_toSignature_2784_, 0);
                lean_inc(v_name_2795_);
                lean_dec_ref(v_toSignature_2784_);
                v___x_2796_ = 1;
                v___x_2797_ = l_Lean_Environment_setExporting(v_env_2794_, v___x_2796_);
                v___x_2798_ =
                    l_Lean_Environment_findAsync_x3f(v___x_2797_, v_name_2795_, v_a_2785_);
                if lean_obj_tag(v___x_2798_) == 0 {
                    v___x_2799_ = lean_box((v_a_2785_) as usize);
                    v___x_2800_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2800_, 0, v___x_2799_);
                    return v___x_2800_;
                } else {
                    v_val_2801_ = lean_ctor_get(v___x_2798_, 0);
                    v_isSharedCheck_2820_ = (!lean_is_exclusive(v___x_2798_)) as u8;
                    if v_isSharedCheck_2820_ == 0 {
                        v___x_2803_ = v___x_2798_;
                        v_isShared_2804_ = v_isSharedCheck_2820_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2801_);
                        lean_dec(v___x_2798_);
                        v___x_2803_ = lean_box(0);
                        v_isShared_2804_ = v_isSharedCheck_2820_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_kind_2805_ = lean_ctor_get_uint8(
                    v_val_2801_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec(v_val_2801_);
                v___x_2806_ = 0;
                v___x_2807_ = l_Lean_instBEqConstantKind_beq(v_kind_2805_, v___x_2806_);
                if v___x_2807_ == 0 {
                    v___x_2808_ = lean_box((v___x_2807_) as usize);
                    if v_isShared_2804_ == 0 {
                        lean_ctor_set_tag(v___x_2803_, 0);
                        lean_ctor_set(v___x_2803_, 0, v___x_2808_);
                        v___x_2810_ = v___x_2803_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
                        v___x_2810_ = v_reuseFailAlloc_2811_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_options_2812_ = lean_ctor_get(v___y_2790_, 2);
                    v___x_2813_ = l_Lean_Compiler_LCNF_compiler_small;
                    v___x_2814_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__0(v_options_2812_, v___x_2813_);
                    v___x_2815_ =
                        l_Lean_Compiler_LCNF_Code_sizeLe(v_pu_2786_, v_code_2787_, v___x_2814_);
                    lean_dec(v___x_2814_);
                    v___x_2816_ = lean_box((v___x_2815_) as usize);
                    if v_isShared_2804_ == 0 {
                        lean_ctor_set_tag(v___x_2803_, 0);
                        lean_ctor_set(v___x_2803_, 0, v___x_2816_);
                        v___x_2818_ = v___x_2803_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2816_);
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
    mut v_toSignature_2821_: *mut LeanObject,
    mut v_a_2822_: *mut LeanObject,
    mut v_pu_2823_: *mut LeanObject,
    mut v_code_2824_: *mut LeanObject,
    mut v___y_2825_: *mut LeanObject,
    mut v___y_2826_: *mut LeanObject,
    mut v___y_2827_: *mut LeanObject,
    mut v___y_2828_: *mut LeanObject,
    mut v___y_2829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_951__boxed_2830_: u8 = 0;
    let mut v_pu_boxed_2831_: u8 = 0;
    let mut v_res_2832_: *mut LeanObject = core::ptr::null_mut();
    v_a_951__boxed_2830_ = (lean_unbox(v_a_2822_) as u8);
    v_pu_boxed_2831_ = (lean_unbox(v_pu_2823_) as u8);
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
    lean_dec(v___y_2828_);
    lean_dec_ref(v___y_2827_);
    lean_dec(v___y_2826_);
    lean_dec_ref(v___y_2825_);
    lean_dec_ref(v_code_2824_);
    return v_res_2832_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(
    mut v_pu_2833_: u8,
    mut v_decl_2834_: *mut LeanObject,
    mut v_a_2835_: *mut LeanObject,
    mut v_a_2836_: *mut LeanObject,
    mut v_a_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_decl_2834_);
    v___x_2840_ =
        l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(v_decl_2834_, v_a_2837_, v_a_2838_);
    if lean_obj_tag(v___x_2840_) == 0 {
        let mut v_a_2841_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2842_: u8 = 0;
        v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
        lean_inc(v_a_2841_);
        v___x_2842_ = (lean_unbox(v_a_2841_) as u8);
        if v___x_2842_ == 0 {
            let mut v_toSignature_2843_: *mut LeanObject = core::ptr::null_mut();
            let mut v_value_2844_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_2846_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_2840_, 1);
            v_toSignature_2843_ = lean_ctor_get(v_decl_2834_, 0);
            lean_inc_ref(v_toSignature_2843_);
            v_value_2844_ = lean_ctor_get(v_decl_2834_, 1);
            lean_inc_ref(v_value_2844_);
            lean_dec_ref(v_decl_2834_);
            v___x_2845_ = lean_box((v_pu_2833_) as usize);
            v___f_2846_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
            lean_closure_set(v___f_2846_, 0, v_toSignature_2843_);
            lean_closure_set(v___f_2846_, 1, v_a_2841_);
            lean_closure_set(v___f_2846_, 2, v___x_2845_);
            v___x_2847_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody_spec__1___redArg(v_value_2844_, v___f_2846_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_);
            return v___x_2847_;
        } else {
            lean_dec(v_a_2841_);
            lean_dec_ref(v_decl_2834_);
            return v___x_2840_;
        }
    } else {
        lean_dec_ref(v_decl_2834_);
        return v___x_2840_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody___boxed(
    mut v_pu_2848_: *mut LeanObject,
    mut v_decl_2849_: *mut LeanObject,
    mut v_a_2850_: *mut LeanObject,
    mut v_a_2851_: *mut LeanObject,
    mut v_a_2852_: *mut LeanObject,
    mut v_a_2853_: *mut LeanObject,
    mut v_a_2854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2855_: u8 = 0;
    let mut v_res_2856_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2855_ = (lean_unbox(v_pu_2848_) as u8);
    v_res_2856_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(
        v_pu_boxed_2855_,
        v_decl_2849_,
        v_a_2850_,
        v_a_2851_,
        v_a_2852_,
        v_a_2853_,
    );
    lean_dec(v_a_2853_);
    lean_dec_ref(v_a_2852_);
    lean_dec(v_a_2851_);
    lean_dec_ref(v_a_2850_);
    return v_res_2856_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    v___x_2857_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2857_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    v___x_2858_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__0,
    );
    v___x_2859_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2859_, 0, v___x_2858_);
    return v___x_2859_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    v___x_2860_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__1,
    );
    v___x_2861_ = lean_unsigned_to_nat(0);
    v___x_2862_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2862_, 0, v___x_2861_);
    lean_ctor_set(v___x_2862_, 1, v___x_2861_);
    lean_ctor_set(v___x_2862_, 2, v___x_2861_);
    lean_ctor_set(v___x_2862_, 3, v___x_2861_);
    lean_ctor_set(v___x_2862_, 4, v___x_2860_);
    lean_ctor_set(v___x_2862_, 5, v___x_2860_);
    lean_ctor_set(v___x_2862_, 6, v___x_2860_);
    lean_ctor_set(v___x_2862_, 7, v___x_2860_);
    lean_ctor_set(v___x_2862_, 8, v___x_2860_);
    lean_ctor_set(v___x_2862_, 9, v___x_2860_);
    return v___x_2862_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3()
-> f64 {
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: f64 = 0.0;
    v___x_2863_ = lean_unsigned_to_nat(0);
    v___x_2864_ = lean_float_of_nat(v___x_2863_);
    return v___x_2864_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(
    mut v_cls_2868_: *mut LeanObject,
    mut v_msg_2869_: *mut LeanObject,
    mut v___y_2870_: *mut LeanObject,
    mut v___y_2871_: *mut LeanObject,
    mut v___y_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2883_: u8 = 0;
    let mut v_env_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2888_: u8 = 0;
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v_tid_2903_: u64 = 0;
    let mut v_traces_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2908_: u8 = 0;
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: f64 = 0.0;
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_isSharedCheck_2936_: u8 = 0;
    let mut v_unused_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2938_: u8 = 0;
    let mut v_a_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2942_: u8 = 0;
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2875_ = lean_ctor_get(v___y_2872_, 2);
                v_ref_2876_ = lean_ctor_get(v___y_2872_, 5);
                v___x_2877_ = lean_st_ref_get(v___y_2873_);
                v___x_2878_ = lean_st_ref_get(v___y_2871_);
                v___x_2879_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2870_);
                if lean_obj_tag(v___x_2879_) == 0 {
                    v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
                    v_isSharedCheck_2938_ = (!lean_is_exclusive(v___x_2879_)) as u8;
                    if v_isSharedCheck_2938_ == 0 {
                        v___x_2882_ = v___x_2879_;
                        v_isShared_2883_ = v_isSharedCheck_2938_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2880_);
                        lean_dec(v___x_2879_);
                        v___x_2882_ = lean_box(0);
                        v_isShared_2883_ = v_isSharedCheck_2938_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2878_);
                    lean_dec(v___x_2877_);
                    lean_dec_ref(v_msg_2869_);
                    lean_dec(v_cls_2868_);
                    v_a_2939_ = lean_ctor_get(v___x_2879_, 0);
                    v_isSharedCheck_2946_ = (!lean_is_exclusive(v___x_2879_)) as u8;
                    if v_isSharedCheck_2946_ == 0 {
                        v___x_2941_ = v___x_2879_;
                        v_isShared_2942_ = v_isSharedCheck_2946_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2939_);
                        lean_dec(v___x_2879_);
                        v___x_2941_ = lean_box(0);
                        v_isShared_2942_ = v_isSharedCheck_2946_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_2884_ = lean_ctor_get(v___x_2877_, 0);
                lean_inc_ref(v_env_2884_);
                lean_dec(v___x_2877_);
                v_lctx_2885_ = lean_ctor_get(v___x_2878_, 0);
                v_isSharedCheck_2936_ = (!lean_is_exclusive(v___x_2878_)) as u8;
                if v_isSharedCheck_2936_ == 0 {
                    v_unused_2937_ = lean_ctor_get(v___x_2878_, 1);
                    lean_dec(v_unused_2937_);
                    v___x_2887_ = v___x_2878_;
                    v_isShared_2888_ = v_isSharedCheck_2936_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_2885_);
                    lean_dec(v___x_2878_);
                    v___x_2887_ = lean_box(0);
                    v_isShared_2888_ = v_isSharedCheck_2936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2889_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
                v___x_2890_ = lean_st_ref_take(v___y_2873_);
                v_traceState_2891_ = lean_ctor_get(v___x_2890_, 4);
                v_env_2892_ = lean_ctor_get(v___x_2890_, 0);
                v_nextMacroScope_2893_ = lean_ctor_get(v___x_2890_, 1);
                v_ngen_2894_ = lean_ctor_get(v___x_2890_, 2);
                v_auxDeclNGen_2895_ = lean_ctor_get(v___x_2890_, 3);
                v_cache_2896_ = lean_ctor_get(v___x_2890_, 5);
                v_messages_2897_ = lean_ctor_get(v___x_2890_, 6);
                v_infoState_2898_ = lean_ctor_get(v___x_2890_, 7);
                v_snapshotTasks_2899_ = lean_ctor_get(v___x_2890_, 8);
                v_isSharedCheck_2935_ = (!lean_is_exclusive(v___x_2890_)) as u8;
                if v_isSharedCheck_2935_ == 0 {
                    v___x_2901_ = v___x_2890_;
                    v_isShared_2902_ = v_isSharedCheck_2935_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2899_);
                    lean_inc(v_infoState_2898_);
                    lean_inc(v_messages_2897_);
                    lean_inc(v_cache_2896_);
                    lean_inc(v_traceState_2891_);
                    lean_inc(v_auxDeclNGen_2895_);
                    lean_inc(v_ngen_2894_);
                    lean_inc(v_nextMacroScope_2893_);
                    lean_inc(v_env_2892_);
                    lean_dec(v___x_2890_);
                    v___x_2901_ = lean_box(0);
                    v_isShared_2902_ = v_isSharedCheck_2935_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_2903_ = lean_ctor_get_uint64(
                    v_traceState_2891_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2904_ = lean_ctor_get(v_traceState_2891_, 0);
                v_isSharedCheck_2934_ = (!lean_is_exclusive(v_traceState_2891_)) as u8;
                if v_isSharedCheck_2934_ == 0 {
                    v___x_2906_ = v_traceState_2891_;
                    v_isShared_2907_ = v_isSharedCheck_2934_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_traces_2904_);
                    lean_dec(v_traceState_2891_);
                    v___x_2906_ = lean_box(0);
                    v_isShared_2907_ = v_isSharedCheck_2934_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2908_ = (lean_unbox(v_a_2880_) as u8);
                lean_dec(v_a_2880_);
                v___x_2909_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2885_, v___x_2908_);
                lean_dec_ref(v_lctx_2885_);
                lean_inc_ref(v_options_2875_);
                v___x_2910_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_2910_, 0, v_env_2884_);
                lean_ctor_set(v___x_2910_, 1, v___x_2889_);
                lean_ctor_set(v___x_2910_, 2, v___x_2909_);
                lean_ctor_set(v___x_2910_, 3, v_options_2875_);
                if v_isShared_2888_ == 0 {
                    lean_ctor_set_tag(v___x_2887_, 3);
                    lean_ctor_set(v___x_2887_, 1, v_msg_2869_);
                    lean_ctor_set(v___x_2887_, 0, v___x_2910_);
                    v___x_2912_ = v___x_2887_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2910_);
                    lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_msg_2869_);
                    v___x_2912_ = v_reuseFailAlloc_2933_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2913_ = lean_box(0);
                v___x_2914_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
                v___x_2915_ = 0;
                v___x_2916_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4;
                v___x_2917_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2917_, 0, v_cls_2868_);
                lean_ctor_set(v___x_2917_, 1, v___x_2913_);
                lean_ctor_set(v___x_2917_, 2, v___x_2916_);
                lean_ctor_set_float(
                    v___x_2917_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2914_,
                );
                lean_ctor_set_float(
                    v___x_2917_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2914_,
                );
                lean_ctor_set_uint8(
                    v___x_2917_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2915_,
                );
                v___x_2918_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5;
                v___x_2919_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2919_, 0, v___x_2917_);
                lean_ctor_set(v___x_2919_, 1, v___x_2912_);
                lean_ctor_set(v___x_2919_, 2, v___x_2918_);
                lean_inc(v_ref_2876_);
                v___x_2920_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2920_, 0, v_ref_2876_);
                lean_ctor_set(v___x_2920_, 1, v___x_2919_);
                v___x_2921_ = l_Lean_PersistentArray_push___redArg(v_traces_2904_, v___x_2920_);
                if v_isShared_2907_ == 0 {
                    lean_ctor_set(v___x_2906_, 0, v___x_2921_);
                    v___x_2923_ = v___x_2906_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2921_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2932_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2903_,
                    );
                    v___x_2923_ = v_reuseFailAlloc_2932_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2902_ == 0 {
                    lean_ctor_set(v___x_2901_, 4, v___x_2923_);
                    v___x_2925_ = v___x_2901_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_env_2892_);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_nextMacroScope_2893_);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 2, v_ngen_2894_);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 3, v_auxDeclNGen_2895_);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 4, v___x_2923_);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 5, v_cache_2896_);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 6, v_messages_2897_);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 7, v_infoState_2898_);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 8, v_snapshotTasks_2899_);
                    v___x_2925_ = v_reuseFailAlloc_2931_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2926_ = lean_st_ref_set(v___y_2873_, v___x_2925_);
                v___x_2927_ = lean_box(0);
                if v_isShared_2883_ == 0 {
                    lean_ctor_set(v___x_2882_, 0, v___x_2927_);
                    v___x_2929_ = v___x_2882_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
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
                    v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
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
    mut v_cls_2947_: *mut LeanObject,
    mut v_msg_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
    mut v___y_2950_: *mut LeanObject,
    mut v___y_2951_: *mut LeanObject,
    mut v___y_2952_: *mut LeanObject,
    mut v___y_2953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2954_: *mut LeanObject = core::ptr::null_mut();
    v_res_2954_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(
        v_cls_2947_,
        v_msg_2948_,
        v___y_2949_,
        v___y_2950_,
        v___y_2951_,
        v___y_2952_,
    );
    lean_dec(v___y_2952_);
    lean_dec_ref(v___y_2951_);
    lean_dec(v___y_2950_);
    lean_dec_ref(v___y_2949_);
    return v_res_2954_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(
    mut v_f_2955_: *mut LeanObject,
    mut v_v_2956_: *mut LeanObject,
    mut v___y_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
    mut v___y_2960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut v_unused_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2956_) == 0 {
                    v_code_2962_ = lean_ctor_get(v_v_2956_, 0);
                    lean_inc_ref(v_code_2962_);
                    lean_dec_ref_known(v_v_2956_, 1);
                    lean_inc(v___y_2960_);
                    lean_inc_ref(v___y_2959_);
                    lean_inc(v___y_2958_);
                    lean_inc_ref(v___y_2957_);
                    v___x_2963_ = lean_apply_6(
                        v_f_2955_,
                        v_code_2962_,
                        v___y_2957_,
                        v___y_2958_,
                        v___y_2959_,
                        v___y_2960_,
                        lean_box(0),
                    );
                    return v___x_2963_;
                } else {
                    lean_dec_ref(v_f_2955_);
                    v_isSharedCheck_2971_ = (!lean_is_exclusive(v_v_2956_)) as u8;
                    if v_isSharedCheck_2971_ == 0 {
                        v_unused_2972_ = lean_ctor_get(v_v_2956_, 0);
                        lean_dec(v_unused_2972_);
                        v___x_2965_ = v_v_2956_;
                        v_isShared_2966_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_v_2956_);
                        v___x_2965_ = lean_box(0);
                        v_isShared_2966_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2967_ = lean_box(0);
                if v_isShared_2966_ == 0 {
                    lean_ctor_set_tag(v___x_2965_, 0);
                    lean_ctor_set(v___x_2965_, 0, v___x_2967_);
                    v___x_2969_ = v___x_2965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
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
    mut v_f_2973_: *mut LeanObject,
    mut v_v_2974_: *mut LeanObject,
    mut v___y_2975_: *mut LeanObject,
    mut v___y_2976_: *mut LeanObject,
    mut v___y_2977_: *mut LeanObject,
    mut v___y_2978_: *mut LeanObject,
    mut v___y_2979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2980_: *mut LeanObject = core::ptr::null_mut();
    v_res_2980_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_2973_, v_v_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
    lean_dec(v___y_2978_);
    lean_dec_ref(v___y_2977_);
    lean_dec(v___y_2976_);
    lean_dec_ref(v___y_2975_);
    return v_res_2980_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(
    mut v_pu_2981_: u8,
    mut v_f_2982_: *mut LeanObject,
    mut v_v_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
    mut v___y_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    v___x_2989_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___redArg(v_f_2982_, v_v_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
    return v___x_2989_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2___boxed(
    mut v_pu_2990_: *mut LeanObject,
    mut v_f_2991_: *mut LeanObject,
    mut v_v_2992_: *mut LeanObject,
    mut v___y_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
    mut v___y_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
    mut v___y_2997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2998_: u8 = 0;
    let mut v_res_2999_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2998_ = (lean_unbox(v_pu_2990_) as u8);
    v_res_2999_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__2(v_pu_boxed_2998_, v_f_2991_, v_v_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
    lean_dec(v___y_2996_);
    lean_dec_ref(v___y_2995_);
    lean_dec(v___y_2994_);
    lean_dec_ref(v___y_2993_);
    return v_res_2999_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0() -> *mut LeanObject {
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    v___x_3000_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3000_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1() -> *mut LeanObject {
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    v___x_3001_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0_once),
        _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__0,
    );
    v___x_3002_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3002_, 0, v___x_3001_);
    return v___x_3002_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2() -> *mut LeanObject {
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    v___x_3003_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1_once),
        _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__1,
    );
    v___x_3004_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3004_, 0, v___x_3003_);
    lean_ctor_set(v___x_3004_, 1, v___x_3003_);
    return v___x_3004_;
}
pub unsafe fn l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed(
    mut v_pu_3005_: *mut LeanObject,
    mut v_phase_3006_: *mut LeanObject,
    mut v_decl_3007_: *mut LeanObject,
    mut v_code_3008_: *mut LeanObject,
    mut v___y_3009_: *mut LeanObject,
    mut v___y_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
    mut v___y_3013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3014_: u8 = 0;
    let mut v_phase_boxed_3015_: u8 = 0;
    let mut v_res_3016_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3014_ = (lean_unbox(v_pu_3005_) as u8);
    v_phase_boxed_3015_ = (lean_unbox(v_phase_3006_) as u8);
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
    lean_dec(v___y_3012_);
    lean_dec_ref(v___y_3011_);
    lean_dec(v___y_3010_);
    lean_dec_ref(v___y_3009_);
    return v_res_3016_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    v___x_3025_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2;
    v___x_3026_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4;
    v___x_3027_ = l_Lean_Name_append(v___x_3026_, v___x_3025_);
    return v___x_3027_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7()
-> *mut LeanObject {
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    v___x_3029_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__6;
    v___x_3030_ = l_Lean_stringToMessageData(v___x_3029_);
    return v___x_3030_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4() -> *mut LeanObject {
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_Lean_Compiler_LCNF_markDeclPublicRec___closed__3;
    v___x_3033_ = l_Lean_stringToMessageData(v___x_3032_);
    return v___x_3033_;
}
pub unsafe fn l_Lean_Compiler_LCNF_markDeclPublicRec(
    mut v_pu_3034_: u8,
    mut v_phase_3035_: u8,
    mut v_decl_3036_: *mut LeanObject,
    mut v_a_3037_: *mut LeanObject,
    mut v_a_3038_: *mut LeanObject,
    mut v_a_3039_: *mut LeanObject,
    mut v_a_3040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3054_: u8 = 0;
    let mut v_value_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: u8 = 0;
    let mut v_env_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: u8 = 0;
    let mut v_options_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3078_: u8 = 0;
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3098_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3105_: u8 = 0;
    let mut v_unused_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_a_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_reuseFailAlloc_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_unused_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3042_ = lean_st_ref_take(v_a_3040_);
                v_toSignature_3043_ = lean_ctor_get(v_decl_3036_, 0);
                v_env_3044_ = lean_ctor_get(v___x_3042_, 0);
                v_nextMacroScope_3045_ = lean_ctor_get(v___x_3042_, 1);
                v_ngen_3046_ = lean_ctor_get(v___x_3042_, 2);
                v_auxDeclNGen_3047_ = lean_ctor_get(v___x_3042_, 3);
                v_traceState_3048_ = lean_ctor_get(v___x_3042_, 4);
                v_messages_3049_ = lean_ctor_get(v___x_3042_, 6);
                v_infoState_3050_ = lean_ctor_get(v___x_3042_, 7);
                v_snapshotTasks_3051_ = lean_ctor_get(v___x_3042_, 8);
                v_isSharedCheck_3126_ = (!lean_is_exclusive(v___x_3042_)) as u8;
                if v_isSharedCheck_3126_ == 0 {
                    v_unused_3127_ = lean_ctor_get(v___x_3042_, 5);
                    lean_dec(v_unused_3127_);
                    v___x_3053_ = v___x_3042_;
                    v_isShared_3054_ = v_isSharedCheck_3126_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3051_);
                    lean_inc(v_infoState_3050_);
                    lean_inc(v_messages_3049_);
                    lean_inc(v_traceState_3048_);
                    lean_inc(v_auxDeclNGen_3047_);
                    lean_inc(v_ngen_3046_);
                    lean_inc(v_nextMacroScope_3045_);
                    lean_inc(v_env_3044_);
                    lean_dec(v___x_3042_);
                    v___x_3053_ = lean_box(0);
                    v_isShared_3054_ = v_isSharedCheck_3126_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_value_3055_ = lean_ctor_get(v_decl_3036_, 1);
                lean_inc_ref(v_value_3055_);
                v_name_3056_ = lean_ctor_get(v_toSignature_3043_, 0);
                lean_inc_n(v_name_3056_, 2);
                v___x_3057_ = l_Lean_Compiler_LCNF_setDeclPublic(v_env_3044_, v_name_3056_);
                v___x_3058_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2,
                );
                if v_isShared_3054_ == 0 {
                    lean_ctor_set(v___x_3053_, 5, v___x_3058_);
                    lean_ctor_set(v___x_3053_, 0, v___x_3057_);
                    v___x_3060_ = v___x_3053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3057_);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_nextMacroScope_3045_);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_ngen_3046_);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 3, v_auxDeclNGen_3047_);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 4, v_traceState_3048_);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 5, v___x_3058_);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 6, v_messages_3049_);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 7, v_infoState_3050_);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 8, v_snapshotTasks_3051_);
                    v___x_3060_ = v_reuseFailAlloc_3125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3061_ = lean_st_ref_set(v_a_3040_, v___x_3060_);
                lean_inc_ref(v_decl_3036_);
                v___x_3062_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_shouldExportBody(v_pu_3034_, v_decl_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
                if lean_obj_tag(v___x_3062_) == 0 {
                    v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
                    v_isSharedCheck_3116_ = (!lean_is_exclusive(v___x_3062_)) as u8;
                    if v_isSharedCheck_3116_ == 0 {
                        v___x_3065_ = v___x_3062_;
                        v_isShared_3066_ = v_isSharedCheck_3116_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3063_);
                        lean_dec(v___x_3062_);
                        v___x_3065_ = lean_box(0);
                        v_isShared_3066_ = v_isSharedCheck_3116_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_name_3056_);
                    lean_dec_ref(v_value_3055_);
                    lean_dec_ref(v_decl_3036_);
                    v_a_3117_ = lean_ctor_get(v___x_3062_, 0);
                    v_isSharedCheck_3124_ = (!lean_is_exclusive(v___x_3062_)) as u8;
                    if v_isSharedCheck_3124_ == 0 {
                        v___x_3119_ = v___x_3062_;
                        v_isShared_3120_ = v_isSharedCheck_3124_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3117_);
                        lean_dec(v___x_3062_);
                        v___x_3119_ = lean_box(0);
                        v_isShared_3120_ = v_isSharedCheck_3124_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3067_ = lean_st_ref_get(v_a_3040_);
                v___x_3073_ = (lean_unbox(v_a_3063_) as u8);
                lean_dec(v_a_3063_);
                if v___x_3073_ == 0 {
                    lean_dec(v___x_3067_);
                    lean_dec(v_name_3056_);
                    lean_dec_ref(v_value_3055_);
                    lean_dec_ref(v_decl_3036_);
                    state = 4;
                    continue;
                } else {
                    v_env_3074_ = lean_ctor_get(v___x_3067_, 0);
                    lean_inc_ref(v_env_3074_);
                    lean_dec(v___x_3067_);
                    v___x_3075_ = l_Lean_Compiler_LCNF_isDeclTransparent(
                        v_env_3074_,
                        v_phase_3035_,
                        v_name_3056_,
                    );
                    if v___x_3075_ == 0 {
                        lean_del_object(v___x_3065_);
                        v_options_3076_ = lean_ctor_get(v_a_3039_, 2);
                        v_inheritedTraceOptions_3077_ = lean_ctor_get(v_a_3039_, 13);
                        v_hasTrace_3078_ = lean_ctor_get_uint8(
                            v_options_3076_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        v___x_3079_ = lean_box((v_pu_3034_) as usize);
                        v___x_3080_ = lean_box((v_phase_3035_) as usize);
                        v___f_3081_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_markDeclPublicRec___lam__0___boxed
                                as *mut core::ffi::c_void,
                            9,
                            3,
                        );
                        lean_closure_set(v___f_3081_, 0, v___x_3079_);
                        lean_closure_set(v___f_3081_, 1, v___x_3080_);
                        lean_closure_set(v___f_3081_, 2, v_decl_3036_);
                        if v_hasTrace_3078_ == 0 {
                            v___y_3083_ = v_a_3037_;
                            v___y_3084_ = v_a_3038_;
                            v___y_3085_ = v_a_3039_;
                            v___y_3086_ = v_a_3040_;
                            state = 6;
                            continue;
                        } else {
                            v___x_3107_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2;
                            v___x_3108_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
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
                                v___x_3110_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
                                lean_inc(v_name_3056_);
                                v___x_3111_ = l_Lean_MessageData_ofName(v_name_3056_);
                                v___x_3112_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3112_, 0, v___x_3110_);
                                lean_ctor_set(v___x_3112_, 1, v___x_3111_);
                                v___x_3113_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4_once
                                    ),
                                    _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__4,
                                );
                                v___x_3114_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3114_, 0, v___x_3112_);
                                lean_ctor_set(v___x_3114_, 1, v___x_3113_);
                                v___x_3115_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_3107_, v___x_3114_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
                                if lean_obj_tag(v___x_3115_) == 0 {
                                    lean_dec_ref_known(v___x_3115_, 1);
                                    v___y_3083_ = v_a_3037_;
                                    v___y_3084_ = v_a_3038_;
                                    v___y_3085_ = v_a_3039_;
                                    v___y_3086_ = v_a_3040_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_dec_ref(v___f_3081_);
                                    lean_dec(v_name_3056_);
                                    lean_dec_ref(v_value_3055_);
                                    return v___x_3115_;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_name_3056_);
                        lean_dec_ref(v_value_3055_);
                        lean_dec_ref(v_decl_3036_);
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3069_ = lean_box(0);
                if v_isShared_3066_ == 0 {
                    lean_ctor_set(v___x_3065_, 0, v___x_3069_);
                    v___x_3071_ = v___x_3065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
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
                v_env_3088_ = lean_ctor_get(v___x_3087_, 0);
                v_nextMacroScope_3089_ = lean_ctor_get(v___x_3087_, 1);
                v_ngen_3090_ = lean_ctor_get(v___x_3087_, 2);
                v_auxDeclNGen_3091_ = lean_ctor_get(v___x_3087_, 3);
                v_traceState_3092_ = lean_ctor_get(v___x_3087_, 4);
                v_messages_3093_ = lean_ctor_get(v___x_3087_, 6);
                v_infoState_3094_ = lean_ctor_get(v___x_3087_, 7);
                v_snapshotTasks_3095_ = lean_ctor_get(v___x_3087_, 8);
                v_isSharedCheck_3105_ = (!lean_is_exclusive(v___x_3087_)) as u8;
                if v_isSharedCheck_3105_ == 0 {
                    v_unused_3106_ = lean_ctor_get(v___x_3087_, 5);
                    lean_dec(v_unused_3106_);
                    v___x_3097_ = v___x_3087_;
                    v_isShared_3098_ = v_isSharedCheck_3105_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3095_);
                    lean_inc(v_infoState_3094_);
                    lean_inc(v_messages_3093_);
                    lean_inc(v_traceState_3092_);
                    lean_inc(v_auxDeclNGen_3091_);
                    lean_inc(v_ngen_3090_);
                    lean_inc(v_nextMacroScope_3089_);
                    lean_inc(v_env_3088_);
                    lean_dec(v___x_3087_);
                    v___x_3097_ = lean_box(0);
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
                    lean_ctor_set(v___x_3097_, 5, v___x_3058_);
                    lean_ctor_set(v___x_3097_, 0, v___x_3099_);
                    v___x_3101_ = v___x_3097_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3099_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_nextMacroScope_3089_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_ngen_3090_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_auxDeclNGen_3091_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 4, v_traceState_3092_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 5, v___x_3058_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 6, v_messages_3093_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 7, v_infoState_3094_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 8, v_snapshotTasks_3095_);
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
                    v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
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
-> *mut LeanObject {
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__8;
    v___x_3130_ = l_Lean_stringToMessageData(v___x_3129_);
    return v___x_3130_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(
    mut v_phase_3131_: u8,
    mut v_decl_3132_: *mut LeanObject,
    mut v_init_3133_: *mut LeanObject,
    mut v_x_3134_: *mut LeanObject,
    mut v___y_3135_: *mut LeanObject,
    mut v___y_3136_: *mut LeanObject,
    mut v___y_3137_: *mut LeanObject,
    mut v___y_3138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: u8 = 0;
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3163_: u8 = 0;
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: u8 = 0;
    let mut v_options_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3168_: u8 = 0;
    let mut v_inheritedTraceOptions_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: u8 = 0;
    let mut v_toSignature_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3186_: u8 = 0;
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3190_: u8 = 0;
    let mut v_a_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3134_) == 0 {
                    v_k_3140_ = lean_ctor_get(v_x_3134_, 1);
                    lean_inc(v_k_3140_);
                    v_l_3141_ = lean_ctor_get(v_x_3134_, 3);
                    lean_inc(v_l_3141_);
                    v_r_3142_ = lean_ctor_get(v_x_3134_, 4);
                    lean_inc(v_r_3142_);
                    lean_dec_ref_known(v_x_3134_, 5);
                    lean_inc_ref(v_decl_3132_);
                    v___x_3143_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_3131_, v_decl_3132_, v_init_3133_, v_l_3141_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
                    if lean_obj_tag(v___x_3143_) == 0 {
                        lean_dec_ref_known(v___x_3143_, 1);
                        v___x_3144_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(
                            v_k_3140_,
                            v_phase_3131_,
                            v___y_3138_,
                        );
                        if lean_obj_tag(v___x_3144_) == 0 {
                            v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
                            lean_inc(v_a_3145_);
                            lean_dec_ref_known(v___x_3144_, 1);
                            v___x_3146_ = lean_box(0);
                            if lean_obj_tag(v_a_3145_) == 1 {
                                v_val_3147_ = lean_ctor_get(v_a_3145_, 0);
                                lean_inc(v_val_3147_);
                                lean_dec_ref_known(v_a_3145_, 1);
                                v___x_3164_ = lean_st_ref_get(v___y_3138_);
                                v_env_3165_ = lean_ctor_get(v___x_3164_, 0);
                                lean_inc_ref(v_env_3165_);
                                lean_dec(v___x_3164_);
                                v___x_3166_ =
                                    l_Lean_Compiler_LCNF_isDeclPublic(v_env_3165_, v_k_3140_);
                                if v___x_3166_ == 0 {
                                    v_options_3167_ = lean_ctor_get(v___y_3137_, 2);
                                    v_hasTrace_3168_ = lean_ctor_get_uint8(
                                        v_options_3167_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                    );
                                    if v_hasTrace_3168_ == 0 {
                                        lean_dec(v_k_3140_);
                                        v___y_3149_ = v___y_3135_;
                                        v___y_3150_ = v___y_3136_;
                                        v___y_3151_ = v___y_3137_;
                                        v___y_3152_ = v___y_3138_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_inheritedTraceOptions_3169_ =
                                            lean_ctor_get(v___y_3137_, 13);
                                        v___x_3170_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2;
                                        v___x_3171_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
                                        v___x_3172_ =
                                            l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                                v_inheritedTraceOptions_3169_,
                                                v_options_3167_,
                                                v___x_3171_,
                                            );
                                        if v___x_3172_ == 0 {
                                            lean_dec(v_k_3140_);
                                            v___y_3149_ = v___y_3135_;
                                            v___y_3150_ = v___y_3136_;
                                            v___y_3151_ = v___y_3137_;
                                            v___y_3152_ = v___y_3138_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_toSignature_3173_ = lean_ctor_get(v_decl_3132_, 0);
                                            v_name_3174_ = lean_ctor_get(v_toSignature_3173_, 0);
                                            v___x_3175_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
                                            v___x_3176_ = l_Lean_MessageData_ofName(v_k_3140_);
                                            v___x_3177_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_3177_, 0, v___x_3175_);
                                            lean_ctor_set(v___x_3177_, 1, v___x_3176_);
                                            v___x_3178_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__9);
                                            v___x_3179_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_3179_, 0, v___x_3177_);
                                            lean_ctor_set(v___x_3179_, 1, v___x_3178_);
                                            lean_inc(v_name_3174_);
                                            v___x_3180_ = l_Lean_MessageData_ofName(v_name_3174_);
                                            v___x_3181_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_3181_, 0, v___x_3179_);
                                            lean_ctor_set(v___x_3181_, 1, v___x_3180_);
                                            v___x_3182_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_3170_, v___x_3181_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
                                            if lean_obj_tag(v___x_3182_) == 0 {
                                                lean_dec_ref_known(v___x_3182_, 1);
                                                v___y_3149_ = v___y_3135_;
                                                v___y_3150_ = v___y_3136_;
                                                v___y_3151_ = v___y_3137_;
                                                v___y_3152_ = v___y_3138_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec(v_val_3147_);
                                                lean_dec(v_r_3142_);
                                                lean_dec_ref(v_decl_3132_);
                                                v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
                                                v_isSharedCheck_3190_ =
                                                    (!lean_is_exclusive(v___x_3182_)) as u8;
                                                if v_isSharedCheck_3190_ == 0 {
                                                    v___x_3185_ = v___x_3182_;
                                                    v_isShared_3186_ = v_isSharedCheck_3190_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3183_);
                                                    lean_dec(v___x_3182_);
                                                    v___x_3185_ = lean_box(0);
                                                    v_isShared_3186_ = v_isSharedCheck_3190_;
                                                    state = 4;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_val_3147_);
                                    lean_dec(v_k_3140_);
                                    v_init_3133_ = v___x_3146_;
                                    v_x_3134_ = v_r_3142_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3145_);
                                lean_dec(v_k_3140_);
                                v_init_3133_ = v___x_3146_;
                                v_x_3134_ = v_r_3142_;
                                state = 0;
                                continue;
                            }
                        } else {
                            lean_dec(v_r_3142_);
                            lean_dec(v_k_3140_);
                            lean_dec_ref(v_decl_3132_);
                            v_a_3193_ = lean_ctor_get(v___x_3144_, 0);
                            v_isSharedCheck_3200_ = (!lean_is_exclusive(v___x_3144_)) as u8;
                            if v_isSharedCheck_3200_ == 0 {
                                v___x_3195_ = v___x_3144_;
                                v_isShared_3196_ = v_isSharedCheck_3200_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3193_);
                                lean_dec(v___x_3144_);
                                v___x_3195_ = lean_box(0);
                                v_isShared_3196_ = v_isSharedCheck_3200_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_r_3142_);
                        lean_dec(v_k_3140_);
                        lean_dec_ref(v_decl_3132_);
                        return v___x_3143_;
                    }
                } else {
                    lean_dec_ref(v_decl_3132_);
                    v___x_3201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3201_, 0, v_init_3133_);
                    v___x_3202_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3202_, 0, v___x_3201_);
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
                if lean_obj_tag(v___x_3154_) == 0 {
                    lean_dec_ref_known(v___x_3154_, 1);
                    v_init_3133_ = v___x_3146_;
                    v_x_3134_ = v_r_3142_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_r_3142_);
                    lean_dec_ref(v_decl_3132_);
                    v_a_3156_ = lean_ctor_get(v___x_3154_, 0);
                    v_isSharedCheck_3163_ = (!lean_is_exclusive(v___x_3154_)) as u8;
                    if v_isSharedCheck_3163_ == 0 {
                        v___x_3158_ = v___x_3154_;
                        v_isShared_3159_ = v_isSharedCheck_3163_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3156_);
                        lean_dec(v___x_3154_);
                        v___x_3158_ = lean_box(0);
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
                    v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
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
                    v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
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
                    v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
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
    mut v_decl_3205_: *mut LeanObject,
    mut v_code_3206_: *mut LeanObject,
    mut v___y_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
    mut v___y_3209_: *mut LeanObject,
    mut v___y_3210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3218_: u8 = 0;
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut v_unused_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3227_: u8 = 0;
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3212_ = l_Lean_NameSet_empty;
                v___x_3213_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_3203_, v_code_3206_, v___x_3212_);
                v___x_3214_ = lean_box(0);
                v___x_3215_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_3204_, v_decl_3205_, v___x_3214_, v___x_3213_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
                if lean_obj_tag(v___x_3215_) == 0 {
                    v_isSharedCheck_3222_ = (!lean_is_exclusive(v___x_3215_)) as u8;
                    if v_isSharedCheck_3222_ == 0 {
                        v_unused_3223_ = lean_ctor_get(v___x_3215_, 0);
                        lean_dec(v_unused_3223_);
                        v___x_3217_ = v___x_3215_;
                        v_isShared_3218_ = v_isSharedCheck_3222_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3215_);
                        v___x_3217_ = lean_box(0);
                        v_isShared_3218_ = v_isSharedCheck_3222_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3224_ = lean_ctor_get(v___x_3215_, 0);
                    v_isSharedCheck_3231_ = (!lean_is_exclusive(v___x_3215_)) as u8;
                    if v_isSharedCheck_3231_ == 0 {
                        v___x_3226_ = v___x_3215_;
                        v_isShared_3227_ = v_isSharedCheck_3231_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3224_);
                        lean_dec(v___x_3215_);
                        v___x_3226_ = lean_box(0);
                        v_isShared_3227_ = v_isSharedCheck_3231_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3218_ == 0 {
                    lean_ctor_set(v___x_3217_, 0, v___x_3214_);
                    v___x_3220_ = v___x_3217_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3214_);
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
                    v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
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
    mut v_phase_3232_: *mut LeanObject,
    mut v_decl_3233_: *mut LeanObject,
    mut v_init_3234_: *mut LeanObject,
    mut v_x_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
    mut v___y_3239_: *mut LeanObject,
    mut v___y_3240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_boxed_3241_: u8 = 0;
    let mut v_res_3242_: *mut LeanObject = core::ptr::null_mut();
    v_phase_boxed_3241_ = (lean_unbox(v_phase_3232_) as u8);
    v_res_3242_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1(v_phase_boxed_3241_, v_decl_3233_, v_init_3234_, v_x_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
    lean_dec(v___y_3239_);
    lean_dec_ref(v___y_3238_);
    lean_dec(v___y_3237_);
    lean_dec_ref(v___y_3236_);
    return v_res_3242_;
}
pub unsafe fn l_Lean_Compiler_LCNF_markDeclPublicRec___boxed(
    mut v_pu_3243_: *mut LeanObject,
    mut v_phase_3244_: *mut LeanObject,
    mut v_decl_3245_: *mut LeanObject,
    mut v_a_3246_: *mut LeanObject,
    mut v_a_3247_: *mut LeanObject,
    mut v_a_3248_: *mut LeanObject,
    mut v_a_3249_: *mut LeanObject,
    mut v_a_3250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3251_: u8 = 0;
    let mut v_phase_boxed_3252_: u8 = 0;
    let mut v_res_3253_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3251_ = (lean_unbox(v_pu_3243_) as u8);
    v_phase_boxed_3252_ = (lean_unbox(v_phase_3244_) as u8);
    v_res_3253_ = l_Lean_Compiler_LCNF_markDeclPublicRec(
        v_pu_boxed_3251_,
        v_phase_boxed_3252_,
        v_decl_3245_,
        v_a_3246_,
        v_a_3247_,
        v_a_3248_,
        v_a_3249_,
    );
    lean_dec(v_a_3249_);
    lean_dec_ref(v_a_3248_);
    lean_dec(v_a_3247_);
    lean_dec_ref(v_a_3246_);
    return v_res_3253_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(
    mut v_msg_3254_: *mut LeanObject,
    mut v___y_3255_: *mut LeanObject,
    mut v___y_3256_: *mut LeanObject,
    mut v___y_3257_: *mut LeanObject,
    mut v___y_3258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v_env_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3274_: u8 = 0;
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v_unused_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_a_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3260_ = lean_ctor_get(v___y_3257_, 2);
                v_ref_3261_ = lean_ctor_get(v___y_3257_, 5);
                v___x_3262_ = lean_st_ref_get(v___y_3258_);
                v___x_3263_ = lean_st_ref_get(v___y_3256_);
                v___x_3264_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3255_);
                if lean_obj_tag(v___x_3264_) == 0 {
                    v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
                    v_isSharedCheck_3287_ = (!lean_is_exclusive(v___x_3264_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v___x_3267_ = v___x_3264_;
                        v_isShared_3268_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3265_);
                        lean_dec(v___x_3264_);
                        v___x_3267_ = lean_box(0);
                        v_isShared_3268_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3263_);
                    lean_dec(v___x_3262_);
                    lean_dec_ref(v_msg_3254_);
                    v_a_3288_ = lean_ctor_get(v___x_3264_, 0);
                    v_isSharedCheck_3295_ = (!lean_is_exclusive(v___x_3264_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3290_ = v___x_3264_;
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3288_);
                        lean_dec(v___x_3264_);
                        v___x_3290_ = lean_box(0);
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_3269_ = lean_ctor_get(v___x_3262_, 0);
                lean_inc_ref(v_env_3269_);
                lean_dec(v___x_3262_);
                v_lctx_3270_ = lean_ctor_get(v___x_3263_, 0);
                v_isSharedCheck_3285_ = (!lean_is_exclusive(v___x_3263_)) as u8;
                if v_isSharedCheck_3285_ == 0 {
                    v_unused_3286_ = lean_ctor_get(v___x_3263_, 1);
                    lean_dec(v_unused_3286_);
                    v___x_3272_ = v___x_3263_;
                    v_isShared_3273_ = v_isSharedCheck_3285_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_3270_);
                    lean_dec(v___x_3263_);
                    v___x_3272_ = lean_box(0);
                    v_isShared_3273_ = v_isSharedCheck_3285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3274_ = (lean_unbox(v_a_3265_) as u8);
                lean_dec(v_a_3265_);
                v___x_3275_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3270_, v___x_3274_);
                lean_dec_ref(v_lctx_3270_);
                v___x_3276_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
                lean_inc_ref(v_options_3260_);
                v___x_3277_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_3277_, 0, v_env_3269_);
                lean_ctor_set(v___x_3277_, 1, v___x_3276_);
                lean_ctor_set(v___x_3277_, 2, v___x_3275_);
                lean_ctor_set(v___x_3277_, 3, v_options_3260_);
                if v_isShared_3273_ == 0 {
                    lean_ctor_set_tag(v___x_3272_, 3);
                    lean_ctor_set(v___x_3272_, 1, v_msg_3254_);
                    lean_ctor_set(v___x_3272_, 0, v___x_3277_);
                    v___x_3279_ = v___x_3272_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3277_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_msg_3254_);
                    v___x_3279_ = v_reuseFailAlloc_3284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_ref_3261_);
                v___x_3280_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3280_, 0, v_ref_3261_);
                lean_ctor_set(v___x_3280_, 1, v___x_3279_);
                if v_isShared_3268_ == 0 {
                    lean_ctor_set_tag(v___x_3267_, 1);
                    lean_ctor_set(v___x_3267_, 0, v___x_3280_);
                    v___x_3282_ = v___x_3267_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
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
                    v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
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
    mut v_msg_3296_: *mut LeanObject,
    mut v___y_3297_: *mut LeanObject,
    mut v___y_3298_: *mut LeanObject,
    mut v___y_3299_: *mut LeanObject,
    mut v___y_3300_: *mut LeanObject,
    mut v___y_3301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3302_: *mut LeanObject = core::ptr::null_mut();
    v_res_3302_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
    lean_dec(v___y_3300_);
    lean_dec_ref(v___y_3299_);
    lean_dec(v___y_3298_);
    lean_dec_ref(v___y_3297_);
    return v_res_3302_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(
    mut v_00_u03b1_3303_: *mut LeanObject,
    mut v_msg_3304_: *mut LeanObject,
    mut v___y_3305_: *mut LeanObject,
    mut v___y_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v_msg_3304_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
    return v___x_3311_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___boxed(
    mut v_00_u03b1_3312_: *mut LeanObject,
    mut v_msg_3313_: *mut LeanObject,
    mut v___y_3314_: *mut LeanObject,
    mut v___y_3315_: *mut LeanObject,
    mut v___y_3316_: *mut LeanObject,
    mut v___y_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3320_: *mut LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0(v_00_u03b1_3312_, v_msg_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
    lean_dec(v___y_3318_);
    lean_dec_ref(v___y_3317_);
    lean_dec(v___y_3316_);
    lean_dec_ref(v___y_3315_);
    lean_dec(v___y_3314_);
    return v_res_3320_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(
    mut v_opts_3321_: *mut LeanObject,
    mut v_opt_3322_: *mut LeanObject,
) -> u8 {
    let mut v_name_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    v_name_3323_ = lean_ctor_get(v_opt_3322_, 0);
    v_defValue_3324_ = lean_ctor_get(v_opt_3322_, 1);
    v_map_3325_ = lean_ctor_get(v_opts_3321_, 0);
    v___x_3326_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3325_,
            v_name_3323_,
        );
    if lean_obj_tag(v___x_3326_) == 0 {
        let mut v___x_3327_: u8 = 0;
        v___x_3327_ = (lean_unbox(v_defValue_3324_) as u8);
        return v___x_3327_;
    } else {
        let mut v_val_3328_: *mut LeanObject = core::ptr::null_mut();
        v_val_3328_ = lean_ctor_get(v___x_3326_, 0);
        lean_inc(v_val_3328_);
        lean_dec_ref_known(v___x_3326_, 1);
        if lean_obj_tag(v_val_3328_) == 1 {
            let mut v_v_3329_: u8 = 0;
            v_v_3329_ = lean_ctor_get_uint8(v_val_3328_, 0 as u32);
            lean_dec_ref_known(v_val_3328_, 0);
            return v_v_3329_;
        } else {
            let mut v___x_3330_: u8 = 0;
            lean_dec(v_val_3328_);
            v___x_3330_ = (lean_unbox(v_defValue_3324_) as u8);
            return v___x_3330_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1___boxed(
    mut v_opts_3331_: *mut LeanObject,
    mut v_opt_3332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3333_: u8 = 0;
    let mut v_r_3334_: *mut LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_opts_3331_, v_opt_3332_);
    lean_dec_ref(v_opt_3332_);
    lean_dec_ref(v_opts_3331_);
    v_r_3334_ = lean_box((v_res_3333_) as usize);
    return v_r_3334_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(
    mut v_f_3335_: *mut LeanObject,
    mut v_v_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3347_: u8 = 0;
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3353_: u8 = 0;
    let mut v_unused_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_3336_) == 0 {
                    v_code_3343_ = lean_ctor_get(v_v_3336_, 0);
                    lean_inc_ref(v_code_3343_);
                    lean_dec_ref_known(v_v_3336_, 1);
                    lean_inc(v___y_3341_);
                    lean_inc_ref(v___y_3340_);
                    lean_inc(v___y_3339_);
                    lean_inc_ref(v___y_3338_);
                    v___x_3344_ = lean_apply_7(
                        v_f_3335_,
                        v_code_3343_,
                        v___y_3337_,
                        v___y_3338_,
                        v___y_3339_,
                        v___y_3340_,
                        v___y_3341_,
                        lean_box(0),
                    );
                    return v___x_3344_;
                } else {
                    lean_dec_ref(v_f_3335_);
                    v_isSharedCheck_3353_ = (!lean_is_exclusive(v_v_3336_)) as u8;
                    if v_isSharedCheck_3353_ == 0 {
                        v_unused_3354_ = lean_ctor_get(v_v_3336_, 0);
                        lean_dec(v_unused_3354_);
                        v___x_3346_ = v_v_3336_;
                        v_isShared_3347_ = v_isSharedCheck_3353_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_v_3336_);
                        v___x_3346_ = lean_box(0);
                        v_isShared_3347_ = v_isSharedCheck_3353_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3348_ = lean_box(0);
                v___x_3349_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3349_, 0, v___x_3348_);
                lean_ctor_set(v___x_3349_, 1, v___y_3337_);
                if v_isShared_3347_ == 0 {
                    lean_ctor_set_tag(v___x_3346_, 0);
                    lean_ctor_set(v___x_3346_, 0, v___x_3349_);
                    v___x_3351_ = v___x_3346_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
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
    mut v_f_3355_: *mut LeanObject,
    mut v_v_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
    mut v___y_3359_: *mut LeanObject,
    mut v___y_3360_: *mut LeanObject,
    mut v___y_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3363_: *mut LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_3355_, v_v_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
    lean_dec(v___y_3361_);
    lean_dec_ref(v___y_3360_);
    lean_dec(v___y_3359_);
    lean_dec_ref(v___y_3358_);
    return v_res_3363_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(
    mut v_pu_3364_: u8,
    mut v_f_3365_: *mut LeanObject,
    mut v_v_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
    mut v___y_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    v___x_3373_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v_f_3365_, v_v_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
    return v___x_3373_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___boxed(
    mut v_pu_3374_: *mut LeanObject,
    mut v_f_3375_: *mut LeanObject,
    mut v_v_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
    mut v___y_3379_: *mut LeanObject,
    mut v___y_3380_: *mut LeanObject,
    mut v___y_3381_: *mut LeanObject,
    mut v___y_3382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3383_: u8 = 0;
    let mut v_res_3384_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3383_ = (lean_unbox(v_pu_3374_) as u8);
    v_res_3384_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3(v_pu_boxed_3383_, v_f_3375_, v_v_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
    lean_dec(v___y_3381_);
    lean_dec_ref(v___y_3380_);
    lean_dec(v___y_3379_);
    lean_dec_ref(v___y_3378_);
    return v_res_3384_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    v___x_3386_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__0;
    v___x_3387_ = l_Lean_stringToMessageData(v___x_3386_);
    return v___x_3387_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    v___x_3389_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__2;
    v___x_3390_ = l_Lean_stringToMessageData(v___x_3389_);
    return v___x_3390_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5()
-> *mut LeanObject {
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    v___x_3392_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__4;
    v___x_3393_ = l_Lean_stringToMessageData(v___x_3392_);
    return v___x_3393_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7()
-> *mut LeanObject {
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    v___x_3395_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__6;
    v___x_3396_ = l_Lean_stringToMessageData(v___x_3395_);
    return v___x_3396_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9()
-> *mut LeanObject {
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v___x_3398_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__8;
    v___x_3399_ = l_Lean_stringToMessageData(v___x_3398_);
    return v___x_3399_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11()
-> *mut LeanObject {
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    v___x_3401_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__10;
    v___x_3402_ = l_Lean_stringToMessageData(v___x_3401_);
    return v___x_3402_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13()
-> *mut LeanObject {
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    v___x_3404_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__12;
    v___x_3405_ = l_Lean_stringToMessageData(v___x_3404_);
    return v___x_3405_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15()
-> *mut LeanObject {
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__14;
    v___x_3408_ = l_Lean_stringToMessageData(v___x_3407_);
    return v___x_3408_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17()
-> *mut LeanObject {
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    v___x_3410_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__16;
    v___x_3411_ = l_Lean_stringToMessageData(v___x_3410_);
    return v___x_3411_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19()
-> *mut LeanObject {
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    v___x_3413_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__18;
    v___x_3414_ = l_Lean_stringToMessageData(v___x_3413_);
    return v___x_3414_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21()
-> *mut LeanObject {
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3416_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__20;
    v___x_3417_ = l_Lean_stringToMessageData(v___x_3416_);
    return v___x_3417_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(
    mut v_pu_3418_: u8,
    mut v_origDecl_3419_: *mut LeanObject,
    mut v_isMeta_3420_: u8,
    mut v_isPublic_3421_: u8,
    mut v_init_3422_: *mut LeanObject,
    mut v_x_3423_: *mut LeanObject,
    mut v___y_3424_: *mut LeanObject,
    mut v___y_3425_: *mut LeanObject,
    mut v___y_3426_: *mut LeanObject,
    mut v___y_3427_: *mut LeanObject,
    mut v___y_3428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: u8 = 0;
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3466_: u8 = 0;
    let mut v_a_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut v_a_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3479_: u8 = 0;
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3483_: u8 = 0;
    let mut v___y_3485_: u8 = 0;
    let mut v___y_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: u8 = 0;
    let mut v___x_3492_: u8 = 0;
    let mut v___x_3494_: u8 = 0;
    let mut v___x_3496_: u8 = 0;
    let mut v___y_3498_: u8 = 0;
    let mut v___y_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3519_: u8 = 0;
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3523_: u8 = 0;
    let mut v_reuseFailAlloc_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3533_: u8 = 0;
    let mut v_toSignature_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3557_: u8 = 0;
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3561_: u8 = 0;
    let mut v___y_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3567_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___y_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3577_: u8 = 0;
    let mut v___x_3578_: u8 = 0;
    let mut v___x_3579_: u8 = 0;
    let mut v___y_3581_: u8 = 0;
    let mut v___y_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: u8 = 0;
    let mut v___y_3589_: u8 = 0;
    let mut v___y_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3596_: u8 = 0;
    let mut v___y_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3602_: u8 = 0;
    let mut v___x_3603_: u8 = 0;
    let mut v___x_3604_: u8 = 0;
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3630_: u8 = 0;
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3634_: u8 = 0;
    let mut v_toSignature_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3650_: u8 = 0;
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3654_: u8 = 0;
    let mut v___y_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3661_: u8 = 0;
    let mut v___x_3662_: u8 = 0;
    let mut v___y_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: u8 = 0;
    let mut v___x_3672_: u8 = 0;
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: u8 = 0;
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3701_: u8 = 0;
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3705_: u8 = 0;
    let mut v___y_3707_: u8 = 0;
    let mut v_modules_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: u8 = 0;
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExported_3713_: u8 = 0;
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3716_: u8 = 0;
    let mut v_toSignature_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3739_: u8 = 0;
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v_modules_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: u8 = 0;
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExported_3749_: u8 = 0;
    let mut v_isSharedCheck_3751_: u8 = 0;
    let mut v_unused_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3423_) == 0 {
                    v_k_3430_ = lean_ctor_get(v_x_3423_, 1);
                    lean_inc(v_k_3430_);
                    v_l_3431_ = lean_ctor_get(v_x_3423_, 3);
                    lean_inc(v_l_3431_);
                    v_r_3432_ = lean_ctor_get(v_x_3423_, 4);
                    lean_inc(v_r_3432_);
                    lean_dec_ref_known(v_x_3423_, 5);
                    lean_inc_ref(v_origDecl_3419_);
                    v___x_3433_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_3418_, v_origDecl_3419_, v_isMeta_3420_, v_isPublic_3421_, v_init_3422_, v_l_3431_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
                    if lean_obj_tag(v___x_3433_) == 0 {
                        v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
                        lean_inc(v_a_3434_);
                        lean_dec_ref_known(v___x_3433_, 1);
                        v_snd_3435_ = lean_ctor_get(v_a_3434_, 1);
                        v_isSharedCheck_3751_ = (!lean_is_exclusive(v_a_3434_)) as u8;
                        if v_isSharedCheck_3751_ == 0 {
                            v_unused_3752_ = lean_ctor_get(v_a_3434_, 0);
                            lean_dec(v_unused_3752_);
                            v___x_3437_ = v_a_3434_;
                            v_isShared_3438_ = v_isSharedCheck_3751_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_3435_);
                            lean_dec(v_a_3434_);
                            v___x_3437_ = lean_box(0);
                            v_isShared_3438_ = v_isSharedCheck_3751_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_r_3432_);
                        lean_dec(v_k_3430_);
                        lean_dec_ref(v_origDecl_3419_);
                        return v___x_3433_;
                    }
                } else {
                    lean_dec_ref(v_origDecl_3419_);
                    v___x_3753_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3753_, 0, v_init_3422_);
                    v___x_3754_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3754_, 0, v___x_3753_);
                    lean_ctor_set(v___x_3754_, 1, v___y_3424_);
                    v___x_3755_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3755_, 0, v___x_3754_);
                    return v___x_3755_;
                }
            }
            1 => {
                v___x_3439_ = lean_box(0);
                v___x_3496_ = l_Lean_NameSet_contains(v_snd_3435_, v_k_3430_);
                if v___x_3496_ == 0 {
                    v___x_3525_ = lean_st_ref_get(v___y_3428_);
                    v_env_3526_ = lean_ctor_get(v___x_3525_, 0);
                    lean_inc_ref(v_env_3526_);
                    lean_dec(v___x_3525_);
                    lean_inc(v_k_3430_);
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
                            if lean_obj_tag(v___x_3674_) == 1 {
                                v_val_3675_ = lean_ctor_get(v___x_3674_, 0);
                                lean_inc(v_val_3675_);
                                lean_dec_ref_known(v___x_3674_, 1);
                                lean_inc(v_k_3430_);
                                lean_inc_ref(v_env_3526_);
                                v___x_3676_ = l_Lean_isMarkedMeta(v_env_3526_, v_k_3430_);
                                if v___x_3676_ == 0 {
                                    v___x_3677_ = l_Lean_Environment_header(v_env_3526_);
                                    v_modules_3708_ = lean_ctor_get(v___x_3677_, 3);
                                    lean_inc_ref(v_modules_3708_);
                                    v___x_3709_ = lean_array_get_size(v_modules_3708_);
                                    v___x_3710_ = lean_nat_dec_lt(v_val_3675_, v___x_3709_);
                                    if v___x_3710_ == 0 {
                                        lean_dec_ref(v_modules_3708_);
                                        v___y_3707_ = v___x_3676_;
                                        state = 31;
                                        continue;
                                    } else {
                                        v___x_3711_ = lean_array_fget(v_modules_3708_, v_val_3675_);
                                        lean_dec_ref(v_modules_3708_);
                                        v_toImport_3712_ = lean_ctor_get(v___x_3711_, 0);
                                        lean_inc_ref(v_toImport_3712_);
                                        lean_dec(v___x_3711_);
                                        v_isExported_3713_ = lean_ctor_get_uint8(
                                            v_toImport_3712_,
                                            (core::mem::size_of::<*mut LeanObject>() * 1 + 1)
                                                as u32,
                                        );
                                        lean_dec_ref(v_toImport_3712_);
                                        if v_isExported_3713_ == 0 {
                                            lean_dec(v___x_3673_);
                                            lean_dec_ref(v_env_3526_);
                                            lean_del_object(v___x_3437_);
                                            lean_dec(v_r_3432_);
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
                                    v_modules_3744_ = lean_ctor_get(v___x_3714_, 3);
                                    lean_inc_ref(v_modules_3744_);
                                    v___x_3745_ = lean_array_get_size(v_modules_3744_);
                                    v___x_3746_ = lean_nat_dec_lt(v_val_3675_, v___x_3745_);
                                    if v___x_3746_ == 0 {
                                        lean_dec_ref(v_modules_3744_);
                                        v___y_3716_ = v___x_3496_;
                                        state = 32;
                                        continue;
                                    } else {
                                        v___x_3747_ = lean_array_fget(v_modules_3744_, v_val_3675_);
                                        lean_dec_ref(v_modules_3744_);
                                        v_toImport_3748_ = lean_ctor_get(v___x_3747_, 0);
                                        lean_inc_ref(v_toImport_3748_);
                                        lean_dec(v___x_3747_);
                                        v_isExported_3749_ = lean_ctor_get_uint8(
                                            v_toImport_3748_,
                                            (core::mem::size_of::<*mut LeanObject>() * 1 + 1)
                                                as u32,
                                        );
                                        lean_dec_ref(v_toImport_3748_);
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
                                lean_dec(v___x_3674_);
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
                    lean_del_object(v___x_3437_);
                    lean_dec(v_k_3430_);
                    v_init_3422_ = v___x_3439_;
                    v_x_3423_ = v_r_3432_;
                    v___y_3424_ = v_snd_3435_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_3446_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_3444_);
                if lean_obj_tag(v___x_3446_) == 0 {
                    v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
                    lean_inc(v_a_3447_);
                    lean_dec_ref_known(v___x_3446_, 1);
                    v___x_3448_ = (lean_unbox(v_a_3447_) as u8);
                    v___x_3449_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(
                        v_k_3430_,
                        v___x_3448_,
                        v___y_3442_,
                    );
                    lean_dec(v_k_3430_);
                    if lean_obj_tag(v___x_3449_) == 0 {
                        v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
                        lean_inc(v_a_3450_);
                        lean_dec_ref_known(v___x_3449_, 1);
                        if lean_obj_tag(v_a_3450_) == 1 {
                            v_val_3451_ = lean_ctor_get(v_a_3450_, 0);
                            lean_inc(v_val_3451_);
                            lean_dec_ref_known(v_a_3450_, 1);
                            v___x_3452_ = (lean_unbox(v_a_3447_) as u8);
                            lean_dec(v_a_3447_);
                            v___x_3453_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_3452_);
                            v___x_3454_ = l_Lean_Compiler_LCNF_Decl_castPurity_x21(
                                v___x_3453_,
                                v_val_3451_,
                                v_pu_3418_,
                            );
                            lean_dec(v_val_3451_);
                            lean_inc_ref(v_origDecl_3419_);
                            v___x_3455_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(v_pu_3418_, v_origDecl_3419_, v_isMeta_3420_, v_isPublic_3421_, v___x_3454_, v___y_3443_, v___y_3444_, v___y_3441_, v___y_3445_, v___y_3442_);
                            if lean_obj_tag(v___x_3455_) == 0 {
                                v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
                                lean_inc(v_a_3456_);
                                lean_dec_ref_known(v___x_3455_, 1);
                                v_snd_3457_ = lean_ctor_get(v_a_3456_, 1);
                                lean_inc(v_snd_3457_);
                                lean_dec(v_a_3456_);
                                v_init_3422_ = v___x_3439_;
                                v_x_3423_ = v_r_3432_;
                                v___y_3424_ = v_snd_3457_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_r_3432_);
                                lean_dec_ref(v_origDecl_3419_);
                                v_a_3459_ = lean_ctor_get(v___x_3455_, 0);
                                v_isSharedCheck_3466_ = (!lean_is_exclusive(v___x_3455_)) as u8;
                                if v_isSharedCheck_3466_ == 0 {
                                    v___x_3461_ = v___x_3455_;
                                    v_isShared_3462_ = v_isSharedCheck_3466_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_3459_);
                                    lean_dec(v___x_3455_);
                                    v___x_3461_ = lean_box(0);
                                    v_isShared_3462_ = v_isSharedCheck_3466_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3450_);
                            lean_dec(v_a_3447_);
                            v_init_3422_ = v___x_3439_;
                            v_x_3423_ = v_r_3432_;
                            v___y_3424_ = v___y_3443_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3447_);
                        lean_dec(v___y_3443_);
                        lean_dec(v_r_3432_);
                        lean_dec_ref(v_origDecl_3419_);
                        v_a_3468_ = lean_ctor_get(v___x_3449_, 0);
                        v_isSharedCheck_3475_ = (!lean_is_exclusive(v___x_3449_)) as u8;
                        if v_isSharedCheck_3475_ == 0 {
                            v___x_3470_ = v___x_3449_;
                            v_isShared_3471_ = v_isSharedCheck_3475_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3468_);
                            lean_dec(v___x_3449_);
                            v___x_3470_ = lean_box(0);
                            v_isShared_3471_ = v_isSharedCheck_3475_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_3443_);
                    lean_dec(v_r_3432_);
                    lean_dec(v_k_3430_);
                    lean_dec_ref(v_origDecl_3419_);
                    v_a_3476_ = lean_ctor_get(v___x_3446_, 0);
                    v_isSharedCheck_3483_ = (!lean_is_exclusive(v___x_3446_)) as u8;
                    if v_isSharedCheck_3483_ == 0 {
                        v___x_3478_ = v___x_3446_;
                        v_isShared_3479_ = v_isSharedCheck_3483_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3476_);
                        lean_dec(v___x_3446_);
                        v___x_3478_ = lean_box(0);
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
                    v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
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
                    v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
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
                    v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
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
                        lean_dec(v_k_3430_);
                        v_init_3422_ = v___x_3439_;
                        v_x_3423_ = v_r_3432_;
                        v___y_3424_ = v___y_3486_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3494_ = l_Lean_isPrivateName(v_k_3430_);
                        if v___x_3494_ == 0 {
                            lean_dec(v_k_3430_);
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
                v_toSignature_3503_ = lean_ctor_get(v_origDecl_3419_, 0);
                lean_inc_ref(v_toSignature_3503_);
                lean_dec_ref(v_origDecl_3419_);
                v_name_3504_ = lean_ctor_get(v_toSignature_3503_, 0);
                lean_inc(v_name_3504_);
                lean_dec_ref(v_toSignature_3503_);
                v___x_3505_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
                v___x_3506_ = l_Lean_MessageData_ofConstName(v_name_3504_, v___x_3496_);
                if v_isShared_3438_ == 0 {
                    lean_ctor_set_tag(v___x_3437_, 7);
                    lean_ctor_set(v___x_3437_, 1, v___x_3506_);
                    lean_ctor_set(v___x_3437_, 0, v___x_3505_);
                    v___x_3508_ = v___x_3437_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3505_);
                    lean_ctor_set(v_reuseFailAlloc_3524_, 1, v___x_3506_);
                    v___x_3508_ = v_reuseFailAlloc_3524_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3509_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
                v___x_3510_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3510_, 0, v___x_3508_);
                lean_ctor_set(v___x_3510_, 1, v___x_3509_);
                v___x_3511_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3496_);
                v___x_3512_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3512_, 0, v___x_3510_);
                lean_ctor_set(v___x_3512_, 1, v___x_3511_);
                v___x_3513_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__5);
                v___x_3514_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3514_, 0, v___x_3512_);
                lean_ctor_set(v___x_3514_, 1, v___x_3513_);
                v___x_3515_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3514_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
                v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
                v_isSharedCheck_3523_ = (!lean_is_exclusive(v___x_3515_)) as u8;
                if v_isSharedCheck_3523_ == 0 {
                    v___x_3518_ = v___x_3515_;
                    v_isShared_3519_ = v_isSharedCheck_3523_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_a_3516_);
                    lean_dec(v___x_3515_);
                    v___x_3518_ = lean_box(0);
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
                    v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
                    v___x_3521_ = v_reuseFailAlloc_3522_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3521_;
            }
            14 => {
                v_toSignature_3534_ = lean_ctor_get(v_origDecl_3419_, 0);
                lean_inc_ref(v_toSignature_3534_);
                lean_dec_ref(v_origDecl_3419_);
                v_name_3535_ = lean_ctor_get(v_toSignature_3534_, 0);
                lean_inc(v_name_3535_);
                lean_dec_ref(v_toSignature_3534_);
                v___x_3536_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__1);
                v___x_3537_ = l_Lean_MessageData_ofConstName(v_name_3535_, v___x_3496_);
                v___x_3538_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3538_, 0, v___x_3536_);
                lean_ctor_set(v___x_3538_, 1, v___x_3537_);
                v___x_3539_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__3);
                v___x_3540_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3540_, 0, v___x_3538_);
                lean_ctor_set(v___x_3540_, 1, v___x_3539_);
                v___x_3541_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3496_);
                v___x_3542_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3542_, 0, v___x_3540_);
                lean_ctor_set(v___x_3542_, 1, v___x_3541_);
                v___x_3543_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__7);
                v___x_3544_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3544_, 0, v___x_3542_);
                lean_ctor_set(v___x_3544_, 1, v___x_3543_);
                v___x_3545_ = lean_box(0);
                v___x_3546_ = l_Lean_Environment_header(v_env_3526_);
                lean_dec_ref(v_env_3526_);
                v___x_3547_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3546_);
                v___x_3548_ = lean_array_get(v___x_3545_, v___x_3547_, v___y_3528_);
                lean_dec(v___y_3528_);
                lean_dec_ref(v___x_3547_);
                v___x_3549_ = l_Lean_MessageData_ofName(v___x_3548_);
                v___x_3550_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3550_, 0, v___x_3544_);
                lean_ctor_set(v___x_3550_, 1, v___x_3549_);
                v___x_3551_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
                v___x_3552_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3552_, 0, v___x_3550_);
                lean_ctor_set(v___x_3552_, 1, v___x_3551_);
                v___x_3553_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3552_, v___y_3531_, v___y_3530_, v___y_3529_, v___y_3532_);
                v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
                v_isSharedCheck_3561_ = (!lean_is_exclusive(v___x_3553_)) as u8;
                if v_isSharedCheck_3561_ == 0 {
                    v___x_3556_ = v___x_3553_;
                    v_isShared_3557_ = v_isSharedCheck_3561_;
                    state = 15;
                    continue;
                } else {
                    lean_inc(v_a_3554_);
                    lean_dec(v___x_3553_);
                    v___x_3556_ = lean_box(0);
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
                    v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
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
                if lean_obj_tag(v___x_3568_) == 1 {
                    v_val_3569_ = lean_ctor_get(v___x_3568_, 0);
                    lean_inc(v_val_3569_);
                    lean_dec_ref_known(v___x_3568_, 1);
                    lean_inc(v_k_3430_);
                    lean_inc_ref(v_env_3526_);
                    v___x_3570_ = l_Lean_isMarkedMeta(v_env_3526_, v_k_3430_);
                    if v___x_3570_ == 0 {
                        lean_del_object(v___x_3437_);
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
                            lean_dec(v_val_3569_);
                            lean_dec_ref(v_env_3526_);
                            v___y_3498_ = v___y_3567_;
                            v___y_3499_ = v___y_3565_;
                            v___y_3500_ = v___y_3563_;
                            v___y_3501_ = v___y_3564_;
                            v___y_3502_ = v___y_3566_;
                            state = 10;
                            continue;
                        } else {
                            lean_del_object(v___x_3437_);
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
                    lean_dec(v___x_3568_);
                    lean_dec_ref(v_env_3526_);
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
                    lean_dec_ref(v_env_3526_);
                    lean_del_object(v___x_3437_);
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
                        lean_dec(v___y_3572_);
                        lean_dec(v_r_3432_);
                        v___y_3563_ = v___y_3574_;
                        v___y_3564_ = v___y_3573_;
                        v___y_3565_ = v___y_3575_;
                        v___y_3566_ = v___y_3576_;
                        v___y_3567_ = v___y_3577_;
                        state = 17;
                        continue;
                    } else {
                        if v___x_3496_ == 0 {
                            lean_dec_ref(v_env_3526_);
                            lean_del_object(v___x_3437_);
                            v___y_3485_ = v___y_3577_;
                            v___y_3486_ = v___y_3572_;
                            v___y_3487_ = v___y_3575_;
                            v___y_3488_ = v___y_3574_;
                            v___y_3489_ = v___y_3573_;
                            v___y_3490_ = v___y_3576_;
                            state = 9;
                            continue;
                        } else {
                            lean_dec(v___y_3572_);
                            lean_dec(v_r_3432_);
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
                    lean_dec_ref(v_env_3526_);
                    lean_del_object(v___x_3437_);
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
                        lean_dec(v___y_3597_);
                        lean_del_object(v___x_3437_);
                        lean_dec(v_r_3432_);
                        v___x_3605_ =
                            l_Lean_Environment_getModuleIdxFor_x3f(v_env_3526_, v_k_3430_);
                        if lean_obj_tag(v___x_3605_) == 1 {
                            v_toSignature_3606_ = lean_ctor_get(v_origDecl_3419_, 0);
                            lean_inc_ref(v_toSignature_3606_);
                            lean_dec_ref(v_origDecl_3419_);
                            v_val_3607_ = lean_ctor_get(v___x_3605_, 0);
                            lean_inc(v_val_3607_);
                            lean_dec_ref_known(v___x_3605_, 1);
                            v_name_3608_ = lean_ctor_get(v_toSignature_3606_, 0);
                            lean_inc(v_name_3608_);
                            lean_dec_ref(v_toSignature_3606_);
                            v___x_3609_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
                            v___x_3610_ = l_Lean_MessageData_ofConstName(v_name_3608_, v___x_3496_);
                            v___x_3611_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3611_, 0, v___x_3609_);
                            lean_ctor_set(v___x_3611_, 1, v___x_3610_);
                            v___x_3612_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
                            v___x_3613_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3613_, 0, v___x_3611_);
                            lean_ctor_set(v___x_3613_, 1, v___x_3612_);
                            v___x_3614_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3496_);
                            v___x_3615_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3615_, 0, v___x_3613_);
                            lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                            v___x_3616_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
                            v___x_3617_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3617_, 0, v___x_3615_);
                            lean_ctor_set(v___x_3617_, 1, v___x_3616_);
                            v___x_3618_ = lean_box(0);
                            v___x_3619_ = l_Lean_Environment_header(v_env_3526_);
                            lean_dec_ref(v_env_3526_);
                            v___x_3620_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3619_);
                            v___x_3621_ = lean_array_get(v___x_3618_, v___x_3620_, v_val_3607_);
                            lean_dec(v_val_3607_);
                            lean_dec_ref(v___x_3620_);
                            v___x_3622_ = l_Lean_MessageData_ofName(v___x_3621_);
                            v___x_3623_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3623_, 0, v___x_3617_);
                            lean_ctor_set(v___x_3623_, 1, v___x_3622_);
                            v___x_3624_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
                            v___x_3625_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3625_, 0, v___x_3623_);
                            lean_ctor_set(v___x_3625_, 1, v___x_3624_);
                            v___x_3626_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3625_, v___y_3601_, v___y_3598_, v___y_3599_, v___y_3600_);
                            v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
                            v_isSharedCheck_3634_ = (!lean_is_exclusive(v___x_3626_)) as u8;
                            if v_isSharedCheck_3634_ == 0 {
                                v___x_3629_ = v___x_3626_;
                                v_isShared_3630_ = v_isSharedCheck_3634_;
                                state = 22;
                                continue;
                            } else {
                                lean_inc(v_a_3627_);
                                lean_dec(v___x_3626_);
                                v___x_3629_ = lean_box(0);
                                v_isShared_3630_ = v_isSharedCheck_3634_;
                                state = 22;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3605_);
                            lean_dec_ref(v_env_3526_);
                            v_toSignature_3635_ = lean_ctor_get(v_origDecl_3419_, 0);
                            lean_inc_ref(v_toSignature_3635_);
                            lean_dec_ref(v_origDecl_3419_);
                            v_name_3636_ = lean_ctor_get(v_toSignature_3635_, 0);
                            lean_inc(v_name_3636_);
                            lean_dec_ref(v_toSignature_3635_);
                            v___x_3637_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__11);
                            v___x_3638_ = l_Lean_MessageData_ofConstName(v_name_3636_, v___x_3496_);
                            v___x_3639_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3639_, 0, v___x_3637_);
                            lean_ctor_set(v___x_3639_, 1, v___x_3638_);
                            v___x_3640_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
                            v___x_3641_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3641_, 0, v___x_3639_);
                            lean_ctor_set(v___x_3641_, 1, v___x_3640_);
                            v___x_3642_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3496_);
                            v___x_3643_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3643_, 0, v___x_3641_);
                            lean_ctor_set(v___x_3643_, 1, v___x_3642_);
                            v___x_3644_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__17);
                            v___x_3645_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3645_, 0, v___x_3643_);
                            lean_ctor_set(v___x_3645_, 1, v___x_3644_);
                            v___x_3646_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3645_, v___y_3601_, v___y_3598_, v___y_3599_, v___y_3600_);
                            v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
                            v_isSharedCheck_3654_ = (!lean_is_exclusive(v___x_3646_)) as u8;
                            if v_isSharedCheck_3654_ == 0 {
                                v___x_3649_ = v___x_3646_;
                                v_isShared_3650_ = v_isSharedCheck_3654_;
                                state = 24;
                                continue;
                            } else {
                                lean_inc(v_a_3647_);
                                lean_dec(v___x_3646_);
                                v___x_3649_ = lean_box(0);
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
                    v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
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
                    v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
                    v___x_3652_ = v_reuseFailAlloc_3653_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3652_;
            }
            26 => {
                lean_inc(v_k_3430_);
                lean_inc_ref(v_env_3526_);
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
                v_options_3669_ = lean_ctor_get(v___y_3667_, 2);
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
                v_toSignature_3679_ = lean_ctor_get(v_origDecl_3419_, 0);
                lean_inc_ref(v_toSignature_3679_);
                lean_dec_ref(v_origDecl_3419_);
                v_name_3680_ = lean_ctor_get(v_toSignature_3679_, 0);
                lean_inc(v_name_3680_);
                lean_dec_ref(v_toSignature_3679_);
                v___x_3681_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
                v___x_3682_ = l_Lean_MessageData_ofConstName(v_name_3680_, v___x_3676_);
                v___x_3683_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3683_, 0, v___x_3681_);
                lean_ctor_set(v___x_3683_, 1, v___x_3682_);
                v___x_3684_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
                v___x_3685_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3685_, 0, v___x_3683_);
                lean_ctor_set(v___x_3685_, 1, v___x_3684_);
                v___x_3686_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3676_);
                v___x_3687_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3687_, 0, v___x_3685_);
                lean_ctor_set(v___x_3687_, 1, v___x_3686_);
                v___x_3688_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__15);
                v___x_3689_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3689_, 0, v___x_3687_);
                lean_ctor_set(v___x_3689_, 1, v___x_3688_);
                v___x_3690_ = lean_box(0);
                v___x_3691_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3677_);
                v___x_3692_ = lean_array_get(v___x_3690_, v___x_3691_, v_val_3675_);
                lean_dec(v_val_3675_);
                lean_dec_ref(v___x_3691_);
                v___x_3693_ = l_Lean_MessageData_ofName(v___x_3692_);
                v___x_3694_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3694_, 0, v___x_3689_);
                lean_ctor_set(v___x_3694_, 1, v___x_3693_);
                v___x_3695_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
                v___x_3696_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3696_, 0, v___x_3694_);
                lean_ctor_set(v___x_3696_, 1, v___x_3695_);
                v___x_3697_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3696_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
                v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
                v_isSharedCheck_3705_ = (!lean_is_exclusive(v___x_3697_)) as u8;
                if v_isSharedCheck_3705_ == 0 {
                    v___x_3700_ = v___x_3697_;
                    v_isShared_3701_ = v_isSharedCheck_3705_;
                    state = 29;
                    continue;
                } else {
                    lean_inc(v_a_3698_);
                    lean_dec(v___x_3697_);
                    v___x_3700_ = lean_box(0);
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
                    v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
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
                    lean_dec_ref(v___x_3677_);
                    lean_dec(v_val_3675_);
                    v___y_3664_ = v___x_3673_;
                    v___y_3665_ = v___y_3425_;
                    v___y_3666_ = v___y_3426_;
                    v___y_3667_ = v___y_3427_;
                    v___y_3668_ = v___y_3428_;
                    state = 27;
                    continue;
                } else {
                    lean_dec(v___x_3673_);
                    lean_dec_ref(v_env_3526_);
                    lean_del_object(v___x_3437_);
                    lean_dec(v_r_3432_);
                    state = 28;
                    continue;
                }
            }
            32 => {
                if v___y_3716_ == 0 {
                    lean_dec_ref(v___x_3714_);
                    lean_dec(v_val_3675_);
                    v___y_3664_ = v___x_3673_;
                    v___y_3665_ = v___y_3425_;
                    v___y_3666_ = v___y_3426_;
                    v___y_3667_ = v___y_3427_;
                    v___y_3668_ = v___y_3428_;
                    state = 27;
                    continue;
                } else {
                    lean_dec(v___x_3673_);
                    lean_dec_ref(v_env_3526_);
                    lean_del_object(v___x_3437_);
                    lean_dec(v_r_3432_);
                    v_toSignature_3717_ = lean_ctor_get(v_origDecl_3419_, 0);
                    lean_inc_ref(v_toSignature_3717_);
                    lean_dec_ref(v_origDecl_3419_);
                    v_name_3718_ = lean_ctor_get(v_toSignature_3717_, 0);
                    lean_inc(v_name_3718_);
                    lean_dec_ref(v_toSignature_3717_);
                    v___x_3719_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__19);
                    v___x_3720_ = l_Lean_MessageData_ofConstName(v_name_3718_, v___x_3496_);
                    v___x_3721_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3721_, 0, v___x_3719_);
                    lean_ctor_set(v___x_3721_, 1, v___x_3720_);
                    v___x_3722_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__13);
                    v___x_3723_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3723_, 0, v___x_3721_);
                    lean_ctor_set(v___x_3723_, 1, v___x_3722_);
                    v___x_3724_ = l_Lean_MessageData_ofConstName(v_k_3430_, v___x_3496_);
                    v___x_3725_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3725_, 0, v___x_3723_);
                    lean_ctor_set(v___x_3725_, 1, v___x_3724_);
                    v___x_3726_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__21);
                    v___x_3727_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3727_, 0, v___x_3725_);
                    lean_ctor_set(v___x_3727_, 1, v___x_3726_);
                    v___x_3728_ = lean_box(0);
                    v___x_3729_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3714_);
                    v___x_3730_ = lean_array_get(v___x_3728_, v___x_3729_, v_val_3675_);
                    lean_dec(v_val_3675_);
                    lean_dec_ref(v___x_3729_);
                    v___x_3731_ = l_Lean_MessageData_ofName(v___x_3730_);
                    v___x_3732_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3732_, 0, v___x_3727_);
                    lean_ctor_set(v___x_3732_, 1, v___x_3731_);
                    v___x_3733_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___closed__9);
                    v___x_3734_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3734_, 0, v___x_3732_);
                    lean_ctor_set(v___x_3734_, 1, v___x_3733_);
                    v___x_3735_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_3734_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
                    v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
                    v_isSharedCheck_3743_ = (!lean_is_exclusive(v___x_3735_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3738_ = v___x_3735_;
                        v_isShared_3739_ = v_isSharedCheck_3743_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_a_3736_);
                        lean_dec(v___x_3735_);
                        v___x_3738_ = lean_box(0);
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
                    v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
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
    mut v_origDecl_3757_: *mut LeanObject,
    mut v_isMeta_3758_: u8,
    mut v_isPublic_3759_: u8,
    mut v_code_3760_: *mut LeanObject,
    mut v___y_3761_: *mut LeanObject,
    mut v___y_3762_: *mut LeanObject,
    mut v___y_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v_snd_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3778_: u8 = 0;
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_unused_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut v_a_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3767_ = l_Lean_NameSet_empty;
                v___x_3768_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v_pu_3756_, v_code_3760_, v___x_3767_);
                v___x_3769_ = lean_box(0);
                v___x_3770_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_3756_, v_origDecl_3757_, v_isMeta_3758_, v_isPublic_3759_, v___x_3769_, v___x_3768_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
                if lean_obj_tag(v___x_3770_) == 0 {
                    v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
                    v_isSharedCheck_3787_ = (!lean_is_exclusive(v___x_3770_)) as u8;
                    if v_isSharedCheck_3787_ == 0 {
                        v___x_3773_ = v___x_3770_;
                        v_isShared_3774_ = v_isSharedCheck_3787_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3771_);
                        lean_dec(v___x_3770_);
                        v___x_3773_ = lean_box(0);
                        v_isShared_3774_ = v_isSharedCheck_3787_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3788_ = lean_ctor_get(v___x_3770_, 0);
                    v_isSharedCheck_3795_ = (!lean_is_exclusive(v___x_3770_)) as u8;
                    if v_isSharedCheck_3795_ == 0 {
                        v___x_3790_ = v___x_3770_;
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3788_);
                        lean_dec(v___x_3770_);
                        v___x_3790_ = lean_box(0);
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3775_ = lean_ctor_get(v_a_3771_, 1);
                v_isSharedCheck_3785_ = (!lean_is_exclusive(v_a_3771_)) as u8;
                if v_isSharedCheck_3785_ == 0 {
                    v_unused_3786_ = lean_ctor_get(v_a_3771_, 0);
                    lean_dec(v_unused_3786_);
                    v___x_3777_ = v_a_3771_;
                    v_isShared_3778_ = v_isSharedCheck_3785_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3775_);
                    lean_dec(v_a_3771_);
                    v___x_3777_ = lean_box(0);
                    v_isShared_3778_ = v_isSharedCheck_3785_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3778_ == 0 {
                    lean_ctor_set(v___x_3777_, 0, v___x_3769_);
                    v___x_3780_ = v___x_3777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3769_);
                    lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_snd_3775_);
                    v___x_3780_ = v_reuseFailAlloc_3784_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3774_ == 0 {
                    lean_ctor_set(v___x_3773_, 0, v___x_3780_);
                    v___x_3782_ = v___x_3773_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3780_);
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
                    v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
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
    mut v_pu_3796_: *mut LeanObject,
    mut v_origDecl_3797_: *mut LeanObject,
    mut v_isMeta_3798_: *mut LeanObject,
    mut v_isPublic_3799_: *mut LeanObject,
    mut v_code_3800_: *mut LeanObject,
    mut v___y_3801_: *mut LeanObject,
    mut v___y_3802_: *mut LeanObject,
    mut v___y_3803_: *mut LeanObject,
    mut v___y_3804_: *mut LeanObject,
    mut v___y_3805_: *mut LeanObject,
    mut v___y_3806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3807_: u8 = 0;
    let mut v_isMeta_boxed_3808_: u8 = 0;
    let mut v_isPublic_boxed_3809_: u8 = 0;
    let mut v_res_3810_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3807_ = (lean_unbox(v_pu_3796_) as u8);
    v_isMeta_boxed_3808_ = (lean_unbox(v_isMeta_3798_) as u8);
    v_isPublic_boxed_3809_ = (lean_unbox(v_isPublic_3799_) as u8);
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
    lean_dec(v___y_3805_);
    lean_dec_ref(v___y_3804_);
    lean_dec(v___y_3803_);
    lean_dec_ref(v___y_3802_);
    return v_res_3810_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go(
    mut v_pu_3811_: u8,
    mut v_origDecl_3812_: *mut LeanObject,
    mut v_isMeta_3813_: u8,
    mut v_isPublic_3814_: u8,
    mut v_decl_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
    mut v_a_3819_: *mut LeanObject,
    mut v_a_3820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    v_value_3822_ = lean_ctor_get(v_decl_3815_, 1);
    lean_inc_ref(v_value_3822_);
    lean_dec_ref(v_decl_3815_);
    v___x_3823_ = lean_box((v_pu_3811_) as usize);
    v___x_3824_ = lean_box((v_isMeta_3813_) as usize);
    v___x_3825_ = lean_box((v_isPublic_3814_) as usize);
    v___f_3826_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
    lean_closure_set(v___f_3826_, 0, v___x_3823_);
    lean_closure_set(v___f_3826_, 1, v_origDecl_3812_);
    lean_closure_set(v___f_3826_, 2, v___x_3824_);
    lean_closure_set(v___f_3826_, 3, v___x_3825_);
    v___x_3827_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_3826_, v_value_3822_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
    return v___x_3827_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go___boxed(
    mut v_pu_3828_: *mut LeanObject,
    mut v_origDecl_3829_: *mut LeanObject,
    mut v_isMeta_3830_: *mut LeanObject,
    mut v_isPublic_3831_: *mut LeanObject,
    mut v_decl_3832_: *mut LeanObject,
    mut v_a_3833_: *mut LeanObject,
    mut v_a_3834_: *mut LeanObject,
    mut v_a_3835_: *mut LeanObject,
    mut v_a_3836_: *mut LeanObject,
    mut v_a_3837_: *mut LeanObject,
    mut v_a_3838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3839_: u8 = 0;
    let mut v_isMeta_boxed_3840_: u8 = 0;
    let mut v_isPublic_boxed_3841_: u8 = 0;
    let mut v_res_3842_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3839_ = (lean_unbox(v_pu_3828_) as u8);
    v_isMeta_boxed_3840_ = (lean_unbox(v_isMeta_3830_) as u8);
    v_isPublic_boxed_3841_ = (lean_unbox(v_isPublic_3831_) as u8);
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
    lean_dec(v_a_3837_);
    lean_dec_ref(v_a_3836_);
    lean_dec(v_a_3835_);
    lean_dec_ref(v_a_3834_);
    return v_res_3842_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2___boxed(
    mut v_pu_3843_: *mut LeanObject,
    mut v_origDecl_3844_: *mut LeanObject,
    mut v_isMeta_3845_: *mut LeanObject,
    mut v_isPublic_3846_: *mut LeanObject,
    mut v_init_3847_: *mut LeanObject,
    mut v_x_3848_: *mut LeanObject,
    mut v___y_3849_: *mut LeanObject,
    mut v___y_3850_: *mut LeanObject,
    mut v___y_3851_: *mut LeanObject,
    mut v___y_3852_: *mut LeanObject,
    mut v___y_3853_: *mut LeanObject,
    mut v___y_3854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3855_: u8 = 0;
    let mut v_isMeta_boxed_3856_: u8 = 0;
    let mut v_isPublic_boxed_3857_: u8 = 0;
    let mut v_res_3858_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3855_ = (lean_unbox(v_pu_3843_) as u8);
    v_isMeta_boxed_3856_ = (lean_unbox(v_isMeta_3845_) as u8);
    v_isPublic_boxed_3857_ = (lean_unbox(v_isPublic_3846_) as u8);
    v_res_3858_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__2(v_pu_boxed_3855_, v_origDecl_3844_, v_isMeta_boxed_3856_, v_isPublic_boxed_3857_, v_init_3847_, v_x_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
    lean_dec(v___y_3853_);
    lean_dec_ref(v___y_3852_);
    lean_dec(v___y_3851_);
    lean_dec_ref(v___y_3850_);
    return v_res_3858_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(
    mut v_opt_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    v_options_3862_ = lean_ctor_get(v___y_3860_, 2);
    v___x_3863_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_3862_, v_opt_3859_);
    v___x_3864_ = lean_box((v___x_3863_) as usize);
    v___x_3865_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3865_, 0, v___x_3864_);
    return v___x_3865_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg___boxed(
    mut v_opt_3866_: *mut LeanObject,
    mut v___y_3867_: *mut LeanObject,
    mut v___y_3868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3869_: *mut LeanObject = core::ptr::null_mut();
    v_res_3869_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(
        v_opt_3866_,
        v___y_3867_,
    );
    lean_dec_ref(v___y_3867_);
    lean_dec_ref(v_opt_3866_);
    return v_res_3869_;
}
pub unsafe fn l_Lean_Compiler_LCNF_checkMeta(
    mut v_pu_3870_: u8,
    mut v_origDecl_3871_: *mut LeanObject,
    mut v_a_3872_: *mut LeanObject,
    mut v_a_3873_: *mut LeanObject,
    mut v_a_3874_: *mut LeanObject,
    mut v_a_3875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3889_: u8 = 0;
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_3897_: u8 = 0;
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: u8 = 0;
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: u8 = 0;
    let mut v___y_3906_: u8 = 0;
    let mut v___x_3907_: u8 = 0;
    let mut v___x_3908_: u8 = 0;
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v_fst_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3919_: u8 = 0;
    let mut v_a_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3929_: u8 = 0;
    let mut v___x_3930_: u8 = 0;
    let mut v___x_3931_: u8 = 0;
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut LeanObject = core::ptr::null_mut();
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
                v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
                v_isSharedCheck_3937_ = (!lean_is_exclusive(v___x_3879_)) as u8;
                if v_isSharedCheck_3937_ == 0 {
                    v___x_3882_ = v___x_3879_;
                    v_isShared_3883_ = v_isSharedCheck_3937_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3880_);
                    lean_dec(v___x_3879_);
                    v___x_3882_ = lean_box(0);
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
                v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
                v_isSharedCheck_3936_ = (!lean_is_exclusive(v___x_3885_)) as u8;
                if v_isSharedCheck_3936_ == 0 {
                    v___x_3888_ = v___x_3885_;
                    v_isShared_3889_ = v_isSharedCheck_3936_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_3886_);
                    lean_dec(v___x_3885_);
                    v___x_3888_ = lean_box(0);
                    v_isShared_3889_ = v_isSharedCheck_3936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_env_3895_ = lean_ctor_get(v___x_3877_, 0);
                lean_inc_ref(v_env_3895_);
                lean_dec(v___x_3877_);
                v___x_3896_ = l_Lean_Environment_header(v_env_3895_);
                lean_dec_ref(v_env_3895_);
                v_isModule_3897_ = lean_ctor_get_uint8(
                    v___x_3896_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 4) as u32,
                );
                lean_dec_ref(v___x_3896_);
                if v_isModule_3897_ == 0 {
                    lean_dec(v_a_3886_);
                    lean_del_object(v___x_3882_);
                    lean_dec(v_a_3880_);
                    lean_dec_ref(v_origDecl_3871_);
                    state = 3;
                    continue;
                } else {
                    v___x_3898_ = (lean_unbox(v_a_3880_) as u8);
                    lean_dec(v_a_3880_);
                    if v___x_3898_ == 0 {
                        v___x_3899_ = (lean_unbox(v_a_3886_) as u8);
                        if v___x_3899_ == 0 {
                            lean_dec(v_a_3886_);
                            lean_del_object(v___x_3882_);
                            lean_dec_ref(v_origDecl_3871_);
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_3888_);
                            v___x_3900_ = lean_st_ref_get(v_a_3875_);
                            v_toSignature_3901_ = lean_ctor_get(v_origDecl_3871_, 0);
                            v_env_3902_ = lean_ctor_get(v___x_3900_, 0);
                            lean_inc_ref(v_env_3902_);
                            lean_dec(v___x_3900_);
                            v_name_3903_ = lean_ctor_get(v_toSignature_3901_, 0);
                            lean_inc(v_name_3903_);
                            v___x_3904_ = l_Lean_getIRPhases(v_env_3902_, v_name_3903_);
                            v___x_3928_ = 2;
                            v___x_3929_ = l_Lean_instBEqIRPhases_beq(v___x_3904_, v___x_3928_);
                            if v___x_3929_ == 0 {
                                lean_del_object(v___x_3882_);
                                v___x_3930_ = l_Lean_isPrivateName(v_name_3903_);
                                if v___x_3930_ == 0 {
                                    v___x_3931_ = (lean_unbox(v_a_3886_) as u8);
                                    lean_dec(v_a_3886_);
                                    v___y_3906_ = v___x_3931_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec(v_a_3886_);
                                    v___y_3906_ = v___x_3929_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3886_);
                                lean_dec_ref(v_origDecl_3871_);
                                v___x_3932_ = lean_box(0);
                                if v_isShared_3883_ == 0 {
                                    lean_ctor_set(v___x_3882_, 0, v___x_3932_);
                                    v___x_3934_ = v___x_3882_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
                                    v___x_3934_ = v_reuseFailAlloc_3935_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_3886_);
                        lean_del_object(v___x_3882_);
                        lean_dec_ref(v_origDecl_3871_);
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3891_ = lean_box(0);
                if v_isShared_3889_ == 0 {
                    lean_ctor_set(v___x_3888_, 0, v___x_3891_);
                    v___x_3893_ = v___x_3888_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
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
                lean_inc_ref(v_origDecl_3871_);
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
                if lean_obj_tag(v___x_3910_) == 0 {
                    v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
                    v_isSharedCheck_3919_ = (!lean_is_exclusive(v___x_3910_)) as u8;
                    if v_isSharedCheck_3919_ == 0 {
                        v___x_3913_ = v___x_3910_;
                        v_isShared_3914_ = v_isSharedCheck_3919_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3911_);
                        lean_dec(v___x_3910_);
                        v___x_3913_ = lean_box(0);
                        v_isShared_3914_ = v_isSharedCheck_3919_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_3920_ = lean_ctor_get(v___x_3910_, 0);
                    v_isSharedCheck_3927_ = (!lean_is_exclusive(v___x_3910_)) as u8;
                    if v_isSharedCheck_3927_ == 0 {
                        v___x_3922_ = v___x_3910_;
                        v_isShared_3923_ = v_isSharedCheck_3927_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3920_);
                        lean_dec(v___x_3910_);
                        v___x_3922_ = lean_box(0);
                        v_isShared_3923_ = v_isSharedCheck_3927_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v_fst_3915_ = lean_ctor_get(v_a_3911_, 0);
                lean_inc(v_fst_3915_);
                lean_dec(v_a_3911_);
                if v_isShared_3914_ == 0 {
                    lean_ctor_set(v___x_3913_, 0, v_fst_3915_);
                    v___x_3917_ = v___x_3913_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_fst_3915_);
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
                    v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
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
    mut v_pu_3938_: *mut LeanObject,
    mut v_origDecl_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
    mut v_a_3941_: *mut LeanObject,
    mut v_a_3942_: *mut LeanObject,
    mut v_a_3943_: *mut LeanObject,
    mut v_a_3944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3945_: u8 = 0;
    let mut v_res_3946_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3945_ = (lean_unbox(v_pu_3938_) as u8);
    v_res_3946_ = l_Lean_Compiler_LCNF_checkMeta(
        v_pu_boxed_3945_,
        v_origDecl_3939_,
        v_a_3940_,
        v_a_3941_,
        v_a_3942_,
        v_a_3943_,
    );
    lean_dec(v_a_3943_);
    lean_dec_ref(v_a_3942_);
    lean_dec(v_a_3941_);
    lean_dec_ref(v_a_3940_);
    return v_res_3946_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(
    mut v_opt_3947_: *mut LeanObject,
    mut v___y_3948_: *mut LeanObject,
    mut v___y_3949_: *mut LeanObject,
    mut v___y_3950_: *mut LeanObject,
    mut v___y_3951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    v___x_3953_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___redArg(
        v_opt_3947_,
        v___y_3950_,
    );
    return v___x_3953_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0___boxed(
    mut v_opt_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
    mut v___y_3956_: *mut LeanObject,
    mut v___y_3957_: *mut LeanObject,
    mut v___y_3958_: *mut LeanObject,
    mut v___y_3959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3960_: *mut LeanObject = core::ptr::null_mut();
    v_res_3960_ = l_Lean_Option_getM___at___00Lean_Compiler_LCNF_checkMeta_spec__0(
        v_opt_3954_,
        v___y_3955_,
        v___y_3956_,
        v___y_3957_,
        v___y_3958_,
    );
    lean_dec(v___y_3958_);
    lean_dec_ref(v___y_3957_);
    lean_dec(v___y_3956_);
    lean_dec_ref(v___y_3955_);
    lean_dec_ref(v_opt_3954_);
    return v_res_3960_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(
    mut v_isExporting_3961_: u8,
    mut v___x_3962_: *mut LeanObject,
    mut v_x_3963_: *mut LeanObject,
    mut v___y_3964_: *mut LeanObject,
    mut v___y_3965_: *mut LeanObject,
    mut v___y_3966_: *mut LeanObject,
    mut v___y_3967_: *mut LeanObject,
    mut v___y_3968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3981_: u8 = 0;
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3990_: u8 = 0;
    let mut v_unused_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3970_ = lean_st_ref_take(v___y_3968_);
                v_env_3971_ = lean_ctor_get(v___x_3970_, 0);
                v_nextMacroScope_3972_ = lean_ctor_get(v___x_3970_, 1);
                v_ngen_3973_ = lean_ctor_get(v___x_3970_, 2);
                v_auxDeclNGen_3974_ = lean_ctor_get(v___x_3970_, 3);
                v_traceState_3975_ = lean_ctor_get(v___x_3970_, 4);
                v_messages_3976_ = lean_ctor_get(v___x_3970_, 6);
                v_infoState_3977_ = lean_ctor_get(v___x_3970_, 7);
                v_snapshotTasks_3978_ = lean_ctor_get(v___x_3970_, 8);
                v_isSharedCheck_3990_ = (!lean_is_exclusive(v___x_3970_)) as u8;
                if v_isSharedCheck_3990_ == 0 {
                    v_unused_3991_ = lean_ctor_get(v___x_3970_, 5);
                    lean_dec(v_unused_3991_);
                    v___x_3980_ = v___x_3970_;
                    v_isShared_3981_ = v_isSharedCheck_3990_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3978_);
                    lean_inc(v_infoState_3977_);
                    lean_inc(v_messages_3976_);
                    lean_inc(v_traceState_3975_);
                    lean_inc(v_auxDeclNGen_3974_);
                    lean_inc(v_ngen_3973_);
                    lean_inc(v_nextMacroScope_3972_);
                    lean_inc(v_env_3971_);
                    lean_dec(v___x_3970_);
                    v___x_3980_ = lean_box(0);
                    v_isShared_3981_ = v_isSharedCheck_3990_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3982_ = l_Lean_Environment_setExporting(v_env_3971_, v_isExporting_3961_);
                if v_isShared_3981_ == 0 {
                    lean_ctor_set(v___x_3980_, 5, v___x_3962_);
                    lean_ctor_set(v___x_3980_, 0, v___x_3982_);
                    v___x_3984_ = v___x_3980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3982_);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 1, v_nextMacroScope_3972_);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 2, v_ngen_3973_);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 3, v_auxDeclNGen_3974_);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 4, v_traceState_3975_);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 5, v___x_3962_);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 6, v_messages_3976_);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 7, v_infoState_3977_);
                    lean_ctor_set(v_reuseFailAlloc_3989_, 8, v_snapshotTasks_3978_);
                    v___x_3984_ = v_reuseFailAlloc_3989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3985_ = lean_st_ref_set(v___y_3968_, v___x_3984_);
                v___x_3986_ = lean_box(0);
                v___x_3987_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3987_, 0, v___x_3986_);
                lean_ctor_set(v___x_3987_, 1, v___y_3964_);
                v___x_3988_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3988_, 0, v___x_3987_);
                return v___x_3988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed(
    mut v_isExporting_3992_: *mut LeanObject,
    mut v___x_3993_: *mut LeanObject,
    mut v_x_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
    mut v___y_3996_: *mut LeanObject,
    mut v___y_3997_: *mut LeanObject,
    mut v___y_3998_: *mut LeanObject,
    mut v___y_3999_: *mut LeanObject,
    mut v___y_4000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_4001_: u8 = 0;
    let mut v_res_4002_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4001_ = (lean_unbox(v_isExporting_3992_) as u8);
    v_res_4002_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0(v_isExporting_boxed_4001_, v___x_3993_, v_x_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
    lean_dec(v___y_3999_);
    lean_dec_ref(v___y_3998_);
    lean_dec(v___y_3997_);
    lean_dec_ref(v___y_3996_);
    lean_dec(v_x_3994_);
    return v_res_4002_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(
    mut v___f_4003_: *mut LeanObject,
    mut v___y_4004_: *mut LeanObject,
    mut v___y_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
    mut v_a_x3f_4009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4016_: u8 = 0;
    let mut v_fst_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_x3f_4009_) == 0 {
                    v___x_4011_ = lean_box(0);
                    lean_inc(v___y_4008_);
                    lean_inc_ref(v___y_4007_);
                    lean_inc(v___y_4006_);
                    lean_inc_ref(v___y_4005_);
                    v___x_4012_ = lean_apply_7(
                        v___f_4003_,
                        v___x_4011_,
                        v___y_4004_,
                        v___y_4005_,
                        v___y_4006_,
                        v___y_4007_,
                        v___y_4008_,
                        lean_box(0),
                    );
                    return v___x_4012_;
                } else {
                    lean_dec(v___y_4004_);
                    v_val_4013_ = lean_ctor_get(v_a_x3f_4009_, 0);
                    v_isSharedCheck_4023_ = (!lean_is_exclusive(v_a_x3f_4009_)) as u8;
                    if v_isSharedCheck_4023_ == 0 {
                        v___x_4015_ = v_a_x3f_4009_;
                        v_isShared_4016_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4013_);
                        lean_dec(v_a_x3f_4009_);
                        v___x_4015_ = lean_box(0);
                        v_isShared_4016_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4017_ = lean_ctor_get(v_val_4013_, 0);
                lean_inc(v_fst_4017_);
                v_snd_4018_ = lean_ctor_get(v_val_4013_, 1);
                lean_inc(v_snd_4018_);
                lean_dec(v_val_4013_);
                if v_isShared_4016_ == 0 {
                    lean_ctor_set(v___x_4015_, 0, v_fst_4017_);
                    v___x_4020_ = v___x_4015_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_fst_4017_);
                    v___x_4020_ = v_reuseFailAlloc_4022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v___y_4008_);
                lean_inc_ref(v___y_4007_);
                lean_inc(v___y_4006_);
                lean_inc_ref(v___y_4005_);
                v___x_4021_ = lean_apply_7(
                    v___f_4003_,
                    v___x_4020_,
                    v_snd_4018_,
                    v___y_4005_,
                    v___y_4006_,
                    v___y_4007_,
                    v___y_4008_,
                    lean_box(0),
                );
                return v___x_4021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1___boxed(
    mut v___f_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
    mut v___y_4027_: *mut LeanObject,
    mut v___y_4028_: *mut LeanObject,
    mut v___y_4029_: *mut LeanObject,
    mut v_a_x3f_4030_: *mut LeanObject,
    mut v___y_4031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4032_: *mut LeanObject = core::ptr::null_mut();
    v_res_4032_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v_a_x3f_4030_);
    lean_dec(v___y_4029_);
    lean_dec_ref(v___y_4028_);
    lean_dec(v___y_4027_);
    lean_dec_ref(v___y_4026_);
    return v_res_4032_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(
    mut v_x_4033_: *mut LeanObject,
    mut v_isExporting_4034_: u8,
    mut v___y_4035_: *mut LeanObject,
    mut v___y_4036_: *mut LeanObject,
    mut v___y_4037_: *mut LeanObject,
    mut v___y_4038_: *mut LeanObject,
    mut v___y_4039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4043_: u8 = 0;
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4067_: u8 = 0;
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4074_: u8 = 0;
    let mut v_fst_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v_unused_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4088_: u8 = 0;
    let mut v_a_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4096_: u8 = 0;
    let mut v_reuseFailAlloc_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_a_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4108_: u8 = 0;
    let mut v_unused_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4113_: u8 = 0;
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut v_reuseFailAlloc_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4119_: u8 = 0;
    let mut v_unused_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4041_ = lean_st_ref_get(v___y_4039_);
                v_env_4042_ = lean_ctor_get(v___x_4041_, 0);
                lean_inc_ref(v_env_4042_);
                lean_dec(v___x_4041_);
                v_isExporting_4043_ = lean_ctor_get_uint8(
                    v_env_4042_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_4042_);
                v___x_4044_ = lean_st_ref_take(v___y_4039_);
                v_env_4045_ = lean_ctor_get(v___x_4044_, 0);
                v_nextMacroScope_4046_ = lean_ctor_get(v___x_4044_, 1);
                v_ngen_4047_ = lean_ctor_get(v___x_4044_, 2);
                v_auxDeclNGen_4048_ = lean_ctor_get(v___x_4044_, 3);
                v_traceState_4049_ = lean_ctor_get(v___x_4044_, 4);
                v_messages_4050_ = lean_ctor_get(v___x_4044_, 6);
                v_infoState_4051_ = lean_ctor_get(v___x_4044_, 7);
                v_snapshotTasks_4052_ = lean_ctor_get(v___x_4044_, 8);
                v_isSharedCheck_4119_ = (!lean_is_exclusive(v___x_4044_)) as u8;
                if v_isSharedCheck_4119_ == 0 {
                    v_unused_4120_ = lean_ctor_get(v___x_4044_, 5);
                    lean_dec(v_unused_4120_);
                    v___x_4054_ = v___x_4044_;
                    v_isShared_4055_ = v_isSharedCheck_4119_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4052_);
                    lean_inc(v_infoState_4051_);
                    lean_inc(v_messages_4050_);
                    lean_inc(v_traceState_4049_);
                    lean_inc(v_auxDeclNGen_4048_);
                    lean_inc(v_ngen_4047_);
                    lean_inc(v_nextMacroScope_4046_);
                    lean_inc(v_env_4045_);
                    lean_dec(v___x_4044_);
                    v___x_4054_ = lean_box(0);
                    v_isShared_4055_ = v_isSharedCheck_4119_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4056_ = l_Lean_Environment_setExporting(v_env_4045_, v_isExporting_4034_);
                v___x_4057_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2,
                );
                if v_isShared_4055_ == 0 {
                    lean_ctor_set(v___x_4054_, 5, v___x_4057_);
                    lean_ctor_set(v___x_4054_, 0, v___x_4056_);
                    v___x_4059_ = v___x_4054_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4056_);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_nextMacroScope_4046_);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 2, v_ngen_4047_);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 3, v_auxDeclNGen_4048_);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 4, v_traceState_4049_);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 5, v___x_4057_);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 6, v_messages_4050_);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 7, v_infoState_4051_);
                    lean_ctor_set(v_reuseFailAlloc_4118_, 8, v_snapshotTasks_4052_);
                    v___x_4059_ = v_reuseFailAlloc_4118_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4060_ = lean_st_ref_set(v___y_4039_, v___x_4059_);
                v___x_4061_ = lean_box((v_isExporting_4043_) as usize);
                v___f_4062_ = lean_alloc_closure(l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                lean_closure_set(v___f_4062_, 0, v___x_4061_);
                lean_closure_set(v___f_4062_, 1, v___x_4057_);
                lean_inc(v___y_4039_);
                lean_inc_ref(v___y_4038_);
                lean_inc(v___y_4037_);
                lean_inc_ref(v___y_4036_);
                lean_inc(v___y_4035_);
                v_r_4063_ = lean_apply_6(
                    v_x_4033_,
                    v___y_4035_,
                    v___y_4036_,
                    v___y_4037_,
                    v___y_4038_,
                    v___y_4039_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_4063_) == 0 {
                    v_a_4064_ = lean_ctor_get(v_r_4063_, 0);
                    v_isSharedCheck_4098_ = (!lean_is_exclusive(v_r_4063_)) as u8;
                    if v_isSharedCheck_4098_ == 0 {
                        v___x_4066_ = v_r_4063_;
                        v_isShared_4067_ = v_isSharedCheck_4098_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4064_);
                        lean_dec(v_r_4063_);
                        v___x_4066_ = lean_box(0);
                        v_isShared_4067_ = v_isSharedCheck_4098_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4099_ = lean_ctor_get(v_r_4063_, 0);
                    lean_inc(v_a_4099_);
                    lean_dec_ref_known(v_r_4063_, 1);
                    v___x_4100_ = lean_box(0);
                    v___x_4101_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_4062_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___x_4100_);
                    if lean_obj_tag(v___x_4101_) == 0 {
                        v_isSharedCheck_4108_ = (!lean_is_exclusive(v___x_4101_)) as u8;
                        if v_isSharedCheck_4108_ == 0 {
                            v_unused_4109_ = lean_ctor_get(v___x_4101_, 0);
                            lean_dec(v_unused_4109_);
                            v___x_4103_ = v___x_4101_;
                            v_isShared_4104_ = v_isSharedCheck_4108_;
                            state = 11;
                            continue;
                        } else {
                            lean_dec(v___x_4101_);
                            v___x_4103_ = lean_box(0);
                            v_isShared_4104_ = v_isSharedCheck_4108_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4099_);
                        v_a_4110_ = lean_ctor_get(v___x_4101_, 0);
                        v_isSharedCheck_4117_ = (!lean_is_exclusive(v___x_4101_)) as u8;
                        if v_isSharedCheck_4117_ == 0 {
                            v___x_4112_ = v___x_4101_;
                            v_isShared_4113_ = v_isSharedCheck_4117_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4110_);
                            lean_dec(v___x_4101_);
                            v___x_4112_ = lean_box(0);
                            v_isShared_4113_ = v_isSharedCheck_4117_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            3 => {
                lean_inc(v_a_4064_);
                if v_isShared_4067_ == 0 {
                    lean_ctor_set_tag(v___x_4066_, 1);
                    v___x_4069_ = v___x_4066_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4064_);
                    v___x_4069_ = v_reuseFailAlloc_4097_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4070_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg___lam__1(v___f_4062_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___x_4069_);
                if lean_obj_tag(v___x_4070_) == 0 {
                    v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
                    v_isSharedCheck_4088_ = (!lean_is_exclusive(v___x_4070_)) as u8;
                    if v_isSharedCheck_4088_ == 0 {
                        v___x_4073_ = v___x_4070_;
                        v_isShared_4074_ = v_isSharedCheck_4088_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4071_);
                        lean_dec(v___x_4070_);
                        v___x_4073_ = lean_box(0);
                        v_isShared_4074_ = v_isSharedCheck_4088_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4064_);
                    v_a_4089_ = lean_ctor_get(v___x_4070_, 0);
                    v_isSharedCheck_4096_ = (!lean_is_exclusive(v___x_4070_)) as u8;
                    if v_isSharedCheck_4096_ == 0 {
                        v___x_4091_ = v___x_4070_;
                        v_isShared_4092_ = v_isSharedCheck_4096_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4089_);
                        lean_dec(v___x_4070_);
                        v___x_4091_ = lean_box(0);
                        v_isShared_4092_ = v_isSharedCheck_4096_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v_fst_4075_ = lean_ctor_get(v_a_4064_, 0);
                lean_inc(v_fst_4075_);
                lean_dec(v_a_4064_);
                v_snd_4076_ = lean_ctor_get(v_a_4071_, 1);
                v_isSharedCheck_4086_ = (!lean_is_exclusive(v_a_4071_)) as u8;
                if v_isSharedCheck_4086_ == 0 {
                    v_unused_4087_ = lean_ctor_get(v_a_4071_, 0);
                    lean_dec(v_unused_4087_);
                    v___x_4078_ = v_a_4071_;
                    v_isShared_4079_ = v_isSharedCheck_4086_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_snd_4076_);
                    lean_dec(v_a_4071_);
                    v___x_4078_ = lean_box(0);
                    v_isShared_4079_ = v_isSharedCheck_4086_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4079_ == 0 {
                    lean_ctor_set(v___x_4078_, 0, v_fst_4075_);
                    v___x_4081_ = v___x_4078_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_fst_4075_);
                    lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_snd_4076_);
                    v___x_4081_ = v_reuseFailAlloc_4085_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4074_ == 0 {
                    lean_ctor_set(v___x_4073_, 0, v___x_4081_);
                    v___x_4083_ = v___x_4073_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4081_);
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
                    v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
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
                    lean_ctor_set_tag(v___x_4103_, 1);
                    lean_ctor_set(v___x_4103_, 0, v_a_4099_);
                    v___x_4106_ = v___x_4103_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4099_);
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
                    v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
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
    mut v_x_4121_: *mut LeanObject,
    mut v_isExporting_4122_: *mut LeanObject,
    mut v___y_4123_: *mut LeanObject,
    mut v___y_4124_: *mut LeanObject,
    mut v___y_4125_: *mut LeanObject,
    mut v___y_4126_: *mut LeanObject,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_4129_: u8 = 0;
    let mut v_res_4130_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4129_ = (lean_unbox(v_isExporting_4122_) as u8);
    v_res_4130_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_4121_, v_isExporting_boxed_4129_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
    lean_dec(v___y_4127_);
    lean_dec_ref(v___y_4126_);
    lean_dec(v___y_4125_);
    lean_dec_ref(v___y_4124_);
    return v_res_4130_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(
    mut v_00_u03b1_4131_: *mut LeanObject,
    mut v_x_4132_: *mut LeanObject,
    mut v_isExporting_4133_: u8,
    mut v___y_4134_: *mut LeanObject,
    mut v___y_4135_: *mut LeanObject,
    mut v___y_4136_: *mut LeanObject,
    mut v___y_4137_: *mut LeanObject,
    mut v___y_4138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v_x_4132_, v_isExporting_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
    return v___x_4140_;
}
pub unsafe fn l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___boxed(
    mut v_00_u03b1_4141_: *mut LeanObject,
    mut v_x_4142_: *mut LeanObject,
    mut v_isExporting_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
    mut v___y_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_4150_: u8 = 0;
    let mut v_res_4151_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4150_ = (lean_unbox(v_isExporting_4143_) as u8);
    v_res_4151_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3(v_00_u03b1_4141_, v_x_4142_, v_isExporting_boxed_4150_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
    lean_dec(v___y_4148_);
    lean_dec_ref(v___y_4147_);
    lean_dec(v___y_4146_);
    lean_dec_ref(v___y_4145_);
    return v_res_4151_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(
    mut v_opt_4152_: *mut LeanObject,
    mut v___y_4153_: *mut LeanObject,
    mut v___y_4154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    v_options_4156_ = lean_ctor_get(v___y_4154_, 2);
    v___x_4157_ = l_Lean_Option_get___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__1(v_options_4156_, v_opt_4152_);
    v___x_4158_ = lean_box((v___x_4157_) as usize);
    v___x_4159_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4159_, 0, v___x_4158_);
    lean_ctor_set(v___x_4159_, 1, v___y_4153_);
    v___x_4160_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4160_, 0, v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg___boxed(
    mut v_opt_4161_: *mut LeanObject,
    mut v___y_4162_: *mut LeanObject,
    mut v___y_4163_: *mut LeanObject,
    mut v___y_4164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4165_: *mut LeanObject = core::ptr::null_mut();
    v_res_4165_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_4161_, v___y_4162_, v___y_4163_);
    lean_dec_ref(v___y_4163_);
    lean_dec_ref(v_opt_4161_);
    return v_res_4165_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(
    mut v_cls_4166_: *mut LeanObject,
    mut v_msg_4167_: *mut LeanObject,
    mut v___y_4168_: *mut LeanObject,
    mut v___y_4169_: *mut LeanObject,
    mut v___y_4170_: *mut LeanObject,
    mut v___y_4171_: *mut LeanObject,
    mut v___y_4172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4182_: u8 = 0;
    let mut v_env_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4201_: u8 = 0;
    let mut v_tid_4202_: u64 = 0;
    let mut v_traces_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4207_: u8 = 0;
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: f64 = 0.0;
    let mut v___x_4214_: u8 = 0;
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4234_: u8 = 0;
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut v_isSharedCheck_4236_: u8 = 0;
    let mut v_unused_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4238_: u8 = 0;
    let mut v_a_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4242_: u8 = 0;
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4174_ = lean_ctor_get(v___y_4171_, 2);
                v_ref_4175_ = lean_ctor_get(v___y_4171_, 5);
                v___x_4176_ = lean_st_ref_get(v___y_4172_);
                v___x_4177_ = lean_st_ref_get(v___y_4170_);
                v___x_4178_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4169_);
                if lean_obj_tag(v___x_4178_) == 0 {
                    v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
                    v_isSharedCheck_4238_ = (!lean_is_exclusive(v___x_4178_)) as u8;
                    if v_isSharedCheck_4238_ == 0 {
                        v___x_4181_ = v___x_4178_;
                        v_isShared_4182_ = v_isSharedCheck_4238_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4179_);
                        lean_dec(v___x_4178_);
                        v___x_4181_ = lean_box(0);
                        v_isShared_4182_ = v_isSharedCheck_4238_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4177_);
                    lean_dec(v___x_4176_);
                    lean_dec(v___y_4168_);
                    lean_dec_ref(v_msg_4167_);
                    lean_dec(v_cls_4166_);
                    v_a_4239_ = lean_ctor_get(v___x_4178_, 0);
                    v_isSharedCheck_4246_ = (!lean_is_exclusive(v___x_4178_)) as u8;
                    if v_isSharedCheck_4246_ == 0 {
                        v___x_4241_ = v___x_4178_;
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4239_);
                        lean_dec(v___x_4178_);
                        v___x_4241_ = lean_box(0);
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_4183_ = lean_ctor_get(v___x_4176_, 0);
                lean_inc_ref(v_env_4183_);
                lean_dec(v___x_4176_);
                v_lctx_4184_ = lean_ctor_get(v___x_4177_, 0);
                v_isSharedCheck_4236_ = (!lean_is_exclusive(v___x_4177_)) as u8;
                if v_isSharedCheck_4236_ == 0 {
                    v_unused_4237_ = lean_ctor_get(v___x_4177_, 1);
                    lean_dec(v_unused_4237_);
                    v___x_4186_ = v___x_4177_;
                    v_isShared_4187_ = v_isSharedCheck_4236_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_4184_);
                    lean_dec(v___x_4177_);
                    v___x_4186_ = lean_box(0);
                    v_isShared_4187_ = v_isSharedCheck_4236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4188_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__2);
                v___x_4189_ = lean_st_ref_take(v___y_4172_);
                v_traceState_4190_ = lean_ctor_get(v___x_4189_, 4);
                v_env_4191_ = lean_ctor_get(v___x_4189_, 0);
                v_nextMacroScope_4192_ = lean_ctor_get(v___x_4189_, 1);
                v_ngen_4193_ = lean_ctor_get(v___x_4189_, 2);
                v_auxDeclNGen_4194_ = lean_ctor_get(v___x_4189_, 3);
                v_cache_4195_ = lean_ctor_get(v___x_4189_, 5);
                v_messages_4196_ = lean_ctor_get(v___x_4189_, 6);
                v_infoState_4197_ = lean_ctor_get(v___x_4189_, 7);
                v_snapshotTasks_4198_ = lean_ctor_get(v___x_4189_, 8);
                v_isSharedCheck_4235_ = (!lean_is_exclusive(v___x_4189_)) as u8;
                if v_isSharedCheck_4235_ == 0 {
                    v___x_4200_ = v___x_4189_;
                    v_isShared_4201_ = v_isSharedCheck_4235_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4198_);
                    lean_inc(v_infoState_4197_);
                    lean_inc(v_messages_4196_);
                    lean_inc(v_cache_4195_);
                    lean_inc(v_traceState_4190_);
                    lean_inc(v_auxDeclNGen_4194_);
                    lean_inc(v_ngen_4193_);
                    lean_inc(v_nextMacroScope_4192_);
                    lean_inc(v_env_4191_);
                    lean_dec(v___x_4189_);
                    v___x_4200_ = lean_box(0);
                    v_isShared_4201_ = v_isSharedCheck_4235_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_4202_ = lean_ctor_get_uint64(
                    v_traceState_4190_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4203_ = lean_ctor_get(v_traceState_4190_, 0);
                v_isSharedCheck_4234_ = (!lean_is_exclusive(v_traceState_4190_)) as u8;
                if v_isSharedCheck_4234_ == 0 {
                    v___x_4205_ = v_traceState_4190_;
                    v_isShared_4206_ = v_isSharedCheck_4234_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_traces_4203_);
                    lean_dec(v_traceState_4190_);
                    v___x_4205_ = lean_box(0);
                    v_isShared_4206_ = v_isSharedCheck_4234_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4207_ = (lean_unbox(v_a_4179_) as u8);
                lean_dec(v_a_4179_);
                v___x_4208_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4184_, v___x_4207_);
                lean_dec_ref(v_lctx_4184_);
                lean_inc_ref(v_options_4174_);
                v___x_4209_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_4209_, 0, v_env_4183_);
                lean_ctor_set(v___x_4209_, 1, v___x_4188_);
                lean_ctor_set(v___x_4209_, 2, v___x_4208_);
                lean_ctor_set(v___x_4209_, 3, v_options_4174_);
                if v_isShared_4187_ == 0 {
                    lean_ctor_set_tag(v___x_4186_, 3);
                    lean_ctor_set(v___x_4186_, 1, v_msg_4167_);
                    lean_ctor_set(v___x_4186_, 0, v___x_4209_);
                    v___x_4211_ = v___x_4186_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4233_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4209_);
                    lean_ctor_set(v_reuseFailAlloc_4233_, 1, v_msg_4167_);
                    v___x_4211_ = v_reuseFailAlloc_4233_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4212_ = lean_box(0);
                v___x_4213_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__3);
                v___x_4214_ = 0;
                v___x_4215_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4;
                v___x_4216_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4216_, 0, v_cls_4166_);
                lean_ctor_set(v___x_4216_, 1, v___x_4212_);
                lean_ctor_set(v___x_4216_, 2, v___x_4215_);
                lean_ctor_set_float(
                    v___x_4216_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4213_,
                );
                lean_ctor_set_float(
                    v___x_4216_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4213_,
                );
                lean_ctor_set_uint8(
                    v___x_4216_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4214_,
                );
                v___x_4217_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__5;
                v___x_4218_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4218_, 0, v___x_4216_);
                lean_ctor_set(v___x_4218_, 1, v___x_4211_);
                lean_ctor_set(v___x_4218_, 2, v___x_4217_);
                lean_inc(v_ref_4175_);
                v___x_4219_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4219_, 0, v_ref_4175_);
                lean_ctor_set(v___x_4219_, 1, v___x_4218_);
                v___x_4220_ = l_Lean_PersistentArray_push___redArg(v_traces_4203_, v___x_4219_);
                if v_isShared_4206_ == 0 {
                    lean_ctor_set(v___x_4205_, 0, v___x_4220_);
                    v___x_4222_ = v___x_4205_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4220_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4232_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4202_,
                    );
                    v___x_4222_ = v_reuseFailAlloc_4232_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4201_ == 0 {
                    lean_ctor_set(v___x_4200_, 4, v___x_4222_);
                    v___x_4224_ = v___x_4200_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_env_4191_);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 1, v_nextMacroScope_4192_);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 2, v_ngen_4193_);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 3, v_auxDeclNGen_4194_);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 4, v___x_4222_);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 5, v_cache_4195_);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 6, v_messages_4196_);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 7, v_infoState_4197_);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 8, v_snapshotTasks_4198_);
                    v___x_4224_ = v_reuseFailAlloc_4231_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4225_ = lean_st_ref_set(v___y_4172_, v___x_4224_);
                v___x_4226_ = lean_box(0);
                v___x_4227_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4227_, 0, v___x_4226_);
                lean_ctor_set(v___x_4227_, 1, v___y_4168_);
                if v_isShared_4182_ == 0 {
                    lean_ctor_set(v___x_4181_, 0, v___x_4227_);
                    v___x_4229_ = v___x_4181_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
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
                    v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
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
    mut v_cls_4247_: *mut LeanObject,
    mut v_msg_4248_: *mut LeanObject,
    mut v___y_4249_: *mut LeanObject,
    mut v___y_4250_: *mut LeanObject,
    mut v___y_4251_: *mut LeanObject,
    mut v___y_4252_: *mut LeanObject,
    mut v___y_4253_: *mut LeanObject,
    mut v___y_4254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4255_: *mut LeanObject = core::ptr::null_mut();
    v_res_4255_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_4247_, v_msg_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
    lean_dec(v___y_4253_);
    lean_dec_ref(v___y_4252_);
    lean_dec(v___y_4251_);
    lean_dec_ref(v___y_4250_);
    return v_res_4255_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(
    mut v_keys_4256_: *mut LeanObject,
    mut v_i_4257_: *mut LeanObject,
    mut v_k_4258_: *mut LeanObject,
) -> u8 {
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: u8 = 0;
    let mut v_k_x27_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: u8 = 0;
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4259_ = lean_array_get_size(v_keys_4256_);
                v___x_4260_ = lean_nat_dec_lt(v_i_4257_, v___x_4259_);
                if v___x_4260_ == 0 {
                    lean_dec(v_i_4257_);
                    return v___x_4260_;
                } else {
                    v_k_x27_4261_ = lean_array_fget_borrowed(v_keys_4256_, v_i_4257_);
                    v___x_4262_ = l_Lean_instBEqExtraModUse_beq(v_k_4258_, v_k_x27_4261_);
                    if v___x_4262_ == 0 {
                        v___x_4263_ = lean_unsigned_to_nat(1);
                        v___x_4264_ = lean_nat_add(v_i_4257_, v___x_4263_);
                        lean_dec(v_i_4257_);
                        v_i_4257_ = v___x_4264_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_4257_);
                        return v___x_4262_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg___boxed(
    mut v_keys_4266_: *mut LeanObject,
    mut v_i_4267_: *mut LeanObject,
    mut v_k_4268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4269_: u8 = 0;
    let mut v_r_4270_: *mut LeanObject = core::ptr::null_mut();
    v_res_4269_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_4266_, v_i_4267_, v_k_4268_);
    lean_dec_ref(v_k_4268_);
    lean_dec_ref(v_keys_4266_);
    v_r_4270_ = lean_box((v_res_4269_) as usize);
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
    v___x_4275_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__0);
    v___x_4276_ = lean_usize_sub(v___x_4275_, v___x_4274_);
    return v___x_4276_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(
    mut v_x_4277_: *mut LeanObject,
    mut v_x_4278_: usize,
    mut v_x_4279_: *mut LeanObject,
) -> u8 {
    let mut v_es_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: usize = 0;
    let mut v___x_4283_: usize = 0;
    let mut v___x_4284_: usize = 0;
    let mut v_j_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: u8 = 0;
    let mut v_node_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: usize = 0;
    let mut v___x_4292_: u8 = 0;
    let mut v_ks_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4277_) == 0 {
                    v_es_4280_ = lean_ctor_get(v_x_4277_, 0);
                    v___x_4281_ = lean_box(2);
                    v___x_4282_ = 5usize;
                    v___x_4283_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1);
                    v___x_4284_ = lean_usize_land(v_x_4278_, v___x_4283_);
                    v_j_4285_ = lean_usize_to_nat(v___x_4284_);
                    v___x_4286_ = lean_array_get_borrowed(v___x_4281_, v_es_4280_, v_j_4285_);
                    lean_dec(v_j_4285_);
                    match lean_obj_tag(v___x_4286_) {
                        0 => {
                            v_key_4287_ = lean_ctor_get(v___x_4286_, 0);
                            v___x_4288_ = l_Lean_instBEqExtraModUse_beq(v_x_4279_, v_key_4287_);
                            return v___x_4288_;
                        }
                        1 => {
                            v_node_4289_ = lean_ctor_get(v___x_4286_, 0);
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
                    v_ks_4293_ = lean_ctor_get(v_x_4277_, 0);
                    v___x_4294_ = lean_unsigned_to_nat(0);
                    v___x_4295_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_ks_4293_, v___x_4294_, v_x_4279_);
                    return v___x_4295_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___boxed(
    mut v_x_4296_: *mut LeanObject,
    mut v_x_4297_: *mut LeanObject,
    mut v_x_4298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_29687__boxed_4299_: usize = 0;
    let mut v_res_4300_: u8 = 0;
    let mut v_r_4301_: *mut LeanObject = core::ptr::null_mut();
    v_x_29687__boxed_4299_ = lean_unbox_usize(v_x_4297_);
    lean_dec(v_x_4297_);
    v_res_4300_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_4296_, v_x_29687__boxed_4299_, v_x_4298_);
    lean_dec_ref(v_x_4298_);
    lean_dec_ref(v_x_4296_);
    v_r_4301_ = lean_box((v_res_4300_) as usize);
    return v_r_4301_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(
    mut v_x_4302_: *mut LeanObject,
    mut v_x_4303_: *mut LeanObject,
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
    mut v_x_4307_: *mut LeanObject,
    mut v_x_4308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4309_: u8 = 0;
    let mut v_r_4310_: *mut LeanObject = core::ptr::null_mut();
    v_res_4309_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_4307_, v_x_4308_);
    lean_dec_ref(v_x_4308_);
    lean_dec_ref(v_x_4307_);
    v_r_4310_ = lean_box((v_res_4309_) as usize);
    return v_r_4310_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    v___x_4313_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__1;
    v___x_4314_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__0;
    v___x_4315_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_4314_, v___x_4313_);
    return v___x_4315_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6()
-> *mut LeanObject {
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    v___x_4320_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__5;
    v___x_4321_ = l_Lean_stringToMessageData(v___x_4320_);
    return v___x_4321_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8()
-> *mut LeanObject {
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    v___x_4323_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__7;
    v___x_4324_ = l_Lean_stringToMessageData(v___x_4323_);
    return v___x_4324_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9()
-> *mut LeanObject {
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    v___x_4325_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0___closed__4;
    v___x_4326_ = l_Lean_stringToMessageData(v___x_4325_);
    return v___x_4326_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10()
-> *mut LeanObject {
    let mut v_cls_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    v_cls_4327_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4;
    v___x_4328_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__4;
    v___x_4329_ = l_Lean_Name_append(v___x_4328_, v_cls_4327_);
    return v___x_4329_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12()
-> *mut LeanObject {
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    v___x_4331_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__11;
    v___x_4332_ = l_Lean_stringToMessageData(v___x_4331_);
    return v___x_4332_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14()
-> *mut LeanObject {
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    v___x_4334_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__13;
    v___x_4335_ = l_Lean_stringToMessageData(v___x_4334_);
    return v___x_4335_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(
    mut v_mod_4340_: *mut LeanObject,
    mut v_isMeta_4341_: u8,
    mut v_hint_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4351_: u8 = 0;
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v_asyncMode_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4385_: u8 = 0;
    let mut v_unused_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: u8 = 0;
    let mut v_options_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4390_: u8 = 0;
    let mut v_inheritedTraceOptions_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: u8 = 0;
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: u8 = 0;
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4349_ = lean_st_ref_get(v___y_4347_);
                v_env_4350_ = lean_ctor_get(v___x_4349_, 0);
                lean_inc_ref(v_env_4350_);
                lean_dec(v___x_4349_);
                v_isExporting_4351_ = lean_ctor_get_uint8(
                    v_env_4350_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_4350_);
                v___x_4352_ = lean_st_ref_get(v___y_4347_);
                v_env_4353_ = lean_ctor_get(v___x_4352_, 0);
                lean_inc_ref(v_env_4353_);
                lean_dec(v___x_4352_);
                v___x_4354_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__2);
                lean_inc(v_mod_4340_);
                v_entry_4355_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_4355_, 0, v_mod_4340_);
                lean_ctor_set_uint8(
                    v_entry_4355_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_4351_,
                );
                lean_ctor_set_uint8(
                    v_entry_4355_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_4341_,
                );
                v___x_4356_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_4357_ = lean_box(1);
                v___x_4358_ = lean_box(0);
                v___x_4387_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4354_,
                    v___x_4356_,
                    v_env_4353_,
                    v___x_4357_,
                    v___x_4358_,
                );
                v___x_4388_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v___x_4387_, v_entry_4355_);
                lean_dec(v___x_4387_);
                if v___x_4388_ == 0 {
                    v_options_4389_ = lean_ctor_get(v___y_4346_, 2);
                    v_hasTrace_4390_ = lean_ctor_get_uint8(
                        v_options_4389_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4390_ == 0 {
                        lean_dec(v_hint_4342_);
                        lean_dec(v_mod_4340_);
                        v___y_4360_ = v___y_4343_;
                        v___y_4361_ = v___y_4347_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4391_ = lean_ctor_get(v___y_4346_, 13);
                        v_cls_4392_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__4;
                        v___x_4414_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__10);
                        v___x_4415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4391_,
                            v_options_4389_,
                            v___x_4414_,
                        );
                        if v___x_4415_ == 0 {
                            lean_dec(v_hint_4342_);
                            lean_dec(v_mod_4340_);
                            v___y_4360_ = v___y_4343_;
                            v___y_4361_ = v___y_4347_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4416_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__12);
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
                    lean_dec_ref_known(v_entry_4355_, 1);
                    lean_dec(v_hint_4342_);
                    lean_dec(v_mod_4340_);
                    v___x_4427_ = lean_box(0);
                    v___x_4428_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4428_, 0, v___x_4427_);
                    lean_ctor_set(v___x_4428_, 1, v___y_4343_);
                    v___x_4429_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4429_, 0, v___x_4428_);
                    return v___x_4429_;
                }
            }
            1 => {
                v___x_4362_ = lean_st_ref_take(v___y_4361_);
                v_toEnvExtension_4363_ = lean_ctor_get(v___x_4356_, 0);
                v_env_4364_ = lean_ctor_get(v___x_4362_, 0);
                v_nextMacroScope_4365_ = lean_ctor_get(v___x_4362_, 1);
                v_ngen_4366_ = lean_ctor_get(v___x_4362_, 2);
                v_auxDeclNGen_4367_ = lean_ctor_get(v___x_4362_, 3);
                v_traceState_4368_ = lean_ctor_get(v___x_4362_, 4);
                v_messages_4369_ = lean_ctor_get(v___x_4362_, 6);
                v_infoState_4370_ = lean_ctor_get(v___x_4362_, 7);
                v_snapshotTasks_4371_ = lean_ctor_get(v___x_4362_, 8);
                v_isSharedCheck_4385_ = (!lean_is_exclusive(v___x_4362_)) as u8;
                if v_isSharedCheck_4385_ == 0 {
                    v_unused_4386_ = lean_ctor_get(v___x_4362_, 5);
                    lean_dec(v_unused_4386_);
                    v___x_4373_ = v___x_4362_;
                    v_isShared_4374_ = v_isSharedCheck_4385_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4371_);
                    lean_inc(v_infoState_4370_);
                    lean_inc(v_messages_4369_);
                    lean_inc(v_traceState_4368_);
                    lean_inc(v_auxDeclNGen_4367_);
                    lean_inc(v_ngen_4366_);
                    lean_inc(v_nextMacroScope_4365_);
                    lean_inc(v_env_4364_);
                    lean_dec(v___x_4362_);
                    v___x_4373_ = lean_box(0);
                    v_isShared_4374_ = v_isSharedCheck_4385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4375_ = lean_ctor_get(v_toEnvExtension_4363_, 2);
                v___x_4376_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4356_,
                    v_env_4364_,
                    v_entry_4355_,
                    v_asyncMode_4375_,
                    v___x_4358_,
                );
                v___x_4377_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_markDeclPublicRec___closed__2,
                );
                if v_isShared_4374_ == 0 {
                    lean_ctor_set(v___x_4373_, 5, v___x_4377_);
                    lean_ctor_set(v___x_4373_, 0, v___x_4376_);
                    v___x_4379_ = v___x_4373_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4376_);
                    lean_ctor_set(v_reuseFailAlloc_4384_, 1, v_nextMacroScope_4365_);
                    lean_ctor_set(v_reuseFailAlloc_4384_, 2, v_ngen_4366_);
                    lean_ctor_set(v_reuseFailAlloc_4384_, 3, v_auxDeclNGen_4367_);
                    lean_ctor_set(v_reuseFailAlloc_4384_, 4, v_traceState_4368_);
                    lean_ctor_set(v_reuseFailAlloc_4384_, 5, v___x_4377_);
                    lean_ctor_set(v_reuseFailAlloc_4384_, 6, v_messages_4369_);
                    lean_ctor_set(v_reuseFailAlloc_4384_, 7, v_infoState_4370_);
                    lean_ctor_set(v_reuseFailAlloc_4384_, 8, v_snapshotTasks_4371_);
                    v___x_4379_ = v_reuseFailAlloc_4384_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4380_ = lean_st_ref_set(v___y_4361_, v___x_4379_);
                v___x_4381_ = lean_box(0);
                v___x_4382_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4382_, 0, v___x_4381_);
                lean_ctor_set(v___x_4382_, 1, v___y_4360_);
                v___x_4383_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4383_, 0, v___x_4382_);
                return v___x_4383_;
            }
            4 => {
                v___x_4396_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4396_, 0, v___y_4394_);
                lean_ctor_set(v___x_4396_, 1, v___y_4395_);
                v___x_4397_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__7(v_cls_4392_, v___x_4396_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
                if lean_obj_tag(v___x_4397_) == 0 {
                    v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
                    lean_inc(v_a_4398_);
                    lean_dec_ref_known(v___x_4397_, 1);
                    v_snd_4399_ = lean_ctor_get(v_a_4398_, 1);
                    lean_inc(v_snd_4399_);
                    lean_dec(v_a_4398_);
                    v___y_4360_ = v_snd_4399_;
                    v___y_4361_ = v___y_4347_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_4355_, 1);
                    return v___x_4397_;
                }
            }
            5 => {
                lean_inc_ref(v___y_4402_);
                v___x_4403_ = l_Lean_stringToMessageData(v___y_4402_);
                v___x_4404_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4404_, 0, v___y_4401_);
                lean_ctor_set(v___x_4404_, 1, v___x_4403_);
                v___x_4405_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__6);
                v___x_4406_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4406_, 0, v___x_4404_);
                lean_ctor_set(v___x_4406_, 1, v___x_4405_);
                v___x_4407_ = l_Lean_MessageData_ofName(v_mod_4340_);
                v___x_4408_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4408_, 0, v___x_4406_);
                lean_ctor_set(v___x_4408_, 1, v___x_4407_);
                v___x_4409_ = l_Lean_Name_isAnonymous(v_hint_4342_);
                if v___x_4409_ == 0 {
                    v___x_4410_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__8);
                    v___x_4411_ = l_Lean_MessageData_ofName(v_hint_4342_);
                    v___x_4412_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4412_, 0, v___x_4410_);
                    lean_ctor_set(v___x_4412_, 1, v___x_4411_);
                    v___y_4394_ = v___x_4408_;
                    v___y_4395_ = v___x_4412_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_hint_4342_);
                    v___x_4413_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__9);
                    v___y_4394_ = v___x_4408_;
                    v___y_4395_ = v___x_4413_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v___y_4418_);
                v___x_4419_ = l_Lean_stringToMessageData(v___y_4418_);
                v___x_4420_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4420_, 0, v___x_4416_);
                lean_ctor_set(v___x_4420_, 1, v___x_4419_);
                v___x_4421_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3___closed__14);
                v___x_4422_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4422_, 0, v___x_4420_);
                lean_ctor_set(v___x_4422_, 1, v___x_4421_);
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
    mut v_mod_4430_: *mut LeanObject,
    mut v_isMeta_4431_: *mut LeanObject,
    mut v_hint_4432_: *mut LeanObject,
    mut v___y_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_4439_: u8 = 0;
    let mut v_res_4440_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4439_ = (lean_unbox(v_isMeta_4431_) as u8);
    v_res_4440_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_mod_4430_, v_isMeta_boxed_4439_, v_hint_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
    lean_dec(v___y_4437_);
    lean_dec_ref(v___y_4436_);
    lean_dec(v___y_4435_);
    lean_dec_ref(v___y_4434_);
    return v_res_4440_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(
    mut v_a_4441_: *mut LeanObject,
    mut v_x_4442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u8 = 0;
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4442_) == 0 {
                    v___x_4443_ = lean_box(0);
                    return v___x_4443_;
                } else {
                    v_key_4444_ = lean_ctor_get(v_x_4442_, 0);
                    v_value_4445_ = lean_ctor_get(v_x_4442_, 1);
                    v_tail_4446_ = lean_ctor_get(v_x_4442_, 2);
                    v___x_4447_ = lean_name_eq(v_key_4444_, v_a_4441_);
                    if v___x_4447_ == 0 {
                        v_x_4442_ = v_tail_4446_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_4445_);
                        v___x_4449_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4449_, 0, v_value_4445_);
                        return v___x_4449_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg___boxed(
    mut v_a_4450_: *mut LeanObject,
    mut v_x_4451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4452_: *mut LeanObject = core::ptr::null_mut();
    v_res_4452_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_4450_, v_x_4451_);
    lean_dec(v_x_4451_);
    lean_dec(v_a_4450_);
    return v_res_4452_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: u64 = 0;
    v___x_4453_ = lean_unsigned_to_nat(1723);
    v___x_4454_ = lean_uint64_of_nat(v___x_4453_);
    return v___x_4454_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(
    mut v_m_4455_: *mut LeanObject,
    mut v_a_4456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: u64 = 0;
    let mut v_hash_4475_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4457_ = lean_ctor_get(v_m_4455_, 1);
                v___x_4458_ = lean_array_get_size(v_buckets_4457_);
                if lean_obj_tag(v_a_4456_) == 0 {
                    v___x_4474_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0);
                    v___y_4460_ = v___x_4474_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4475_ = lean_ctor_get_uint64(
                        v_a_4456_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_4476_: *mut LeanObject,
    mut v_a_4477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4478_: *mut LeanObject = core::ptr::null_mut();
    v_res_4478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_4476_, v_a_4477_);
    lean_dec(v_a_4477_);
    lean_dec_ref(v_m_4476_);
    return v_res_4478_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(
    mut v___x_4479_: *mut LeanObject,
    mut v_declName_4480_: *mut LeanObject,
    mut v_as_4481_: *mut LeanObject,
    mut v_sz_4482_: usize,
    mut v_i_4483_: usize,
    mut v_b_4484_: *mut LeanObject,
    mut v___y_4485_: *mut LeanObject,
    mut v___y_4486_: *mut LeanObject,
    mut v___y_4487_: *mut LeanObject,
    mut v___y_4488_: *mut LeanObject,
    mut v___y_4489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4491_: u8 = 0;
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: usize = 0;
    let mut v___x_4507_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4491_ = lean_usize_dec_lt(v_i_4483_, v_sz_4482_);
                if v___x_4491_ == 0 {
                    lean_dec(v_declName_4480_);
                    v___x_4492_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4492_, 0, v_b_4484_);
                    lean_ctor_set(v___x_4492_, 1, v___y_4485_);
                    v___x_4493_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4493_, 0, v___x_4492_);
                    return v___x_4493_;
                } else {
                    v___x_4494_ = l_Lean_Environment_header(v___x_4479_);
                    v_modules_4495_ = lean_ctor_get(v___x_4494_, 3);
                    lean_inc_ref(v_modules_4495_);
                    lean_dec_ref(v___x_4494_);
                    v___x_4496_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_4497_ = lean_array_uget_borrowed(v_as_4481_, v_i_4483_);
                    v___x_4498_ = lean_array_get(v___x_4496_, v_modules_4495_, v_a_4497_);
                    lean_dec_ref(v_modules_4495_);
                    v_toImport_4499_ = lean_ctor_get(v___x_4498_, 0);
                    lean_inc_ref(v_toImport_4499_);
                    lean_dec(v___x_4498_);
                    v_module_4500_ = lean_ctor_get(v_toImport_4499_, 0);
                    lean_inc(v_module_4500_);
                    lean_dec_ref(v_toImport_4499_);
                    v___x_4501_ = 0;
                    lean_inc(v_declName_4480_);
                    v___x_4502_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_4500_, v___x_4501_, v_declName_4480_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
                    if lean_obj_tag(v___x_4502_) == 0 {
                        v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
                        lean_inc(v_a_4503_);
                        lean_dec_ref_known(v___x_4502_, 1);
                        v_snd_4504_ = lean_ctor_get(v_a_4503_, 1);
                        lean_inc(v_snd_4504_);
                        lean_dec(v_a_4503_);
                        v___x_4505_ = lean_box(0);
                        v___x_4506_ = 1usize;
                        v___x_4507_ = lean_usize_add(v_i_4483_, v___x_4506_);
                        v_i_4483_ = v___x_4507_;
                        v_b_4484_ = v___x_4505_;
                        v___y_4485_ = v_snd_4504_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_4480_);
                        return v___x_4502_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4___boxed(
    mut v___x_4509_: *mut LeanObject,
    mut v_declName_4510_: *mut LeanObject,
    mut v_as_4511_: *mut LeanObject,
    mut v_sz_4512_: *mut LeanObject,
    mut v_i_4513_: *mut LeanObject,
    mut v_b_4514_: *mut LeanObject,
    mut v___y_4515_: *mut LeanObject,
    mut v___y_4516_: *mut LeanObject,
    mut v___y_4517_: *mut LeanObject,
    mut v___y_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
    mut v___y_4520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4521_: usize = 0;
    let mut v_i_boxed_4522_: usize = 0;
    let mut v_res_4523_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4521_ = lean_unbox_usize(v_sz_4512_);
    lean_dec(v_sz_4512_);
    v_i_boxed_4522_ = lean_unbox_usize(v_i_4513_);
    lean_dec(v_i_4513_);
    v_res_4523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v___x_4509_, v_declName_4510_, v_as_4511_, v_sz_boxed_4521_, v_i_boxed_4522_, v_b_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
    lean_dec(v___y_4519_);
    lean_dec_ref(v___y_4518_);
    lean_dec(v___y_4517_);
    lean_dec_ref(v___y_4516_);
    lean_dec_ref(v_as_4511_);
    lean_dec_ref(v___x_4509_);
    return v_res_4523_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    v___x_4526_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1;
    v___x_4527_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0;
    v___x_4528_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_4527_, v___x_4526_);
    return v___x_4528_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(
    mut v_declName_4531_: *mut LeanObject,
    mut v_isMeta_4532_: u8,
    mut v___y_4533_: *mut LeanObject,
    mut v___y_4534_: *mut LeanObject,
    mut v___y_4535_: *mut LeanObject,
    mut v___y_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4549_: usize = 0;
    let mut v___x_4550_: usize = 0;
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v_snd_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4559_: u8 = 0;
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4566_: u8 = 0;
    let mut v_unused_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: u8 = 0;
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4580_: u8 = 0;
    let mut v_toImport_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: u8 = 0;
    let mut v___x_4594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4539_ = lean_st_ref_get(v___y_4537_);
                v_env_4544_ = lean_ctor_get(v___x_4539_, 0);
                lean_inc_ref(v_env_4544_);
                lean_dec(v___x_4539_);
                v___x_4569_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4544_, v_declName_4531_);
                if lean_obj_tag(v___x_4569_) == 0 {
                    lean_dec_ref(v_env_4544_);
                    lean_dec(v_declName_4531_);
                    state = 1;
                    continue;
                } else {
                    v_val_4570_ = lean_ctor_get(v___x_4569_, 0);
                    lean_inc(v_val_4570_);
                    lean_dec_ref_known(v___x_4569_, 1);
                    v___x_4571_ = l_Lean_Environment_header(v_env_4544_);
                    v_modules_4572_ = lean_ctor_get(v___x_4571_, 3);
                    lean_inc_ref(v_modules_4572_);
                    lean_dec_ref(v___x_4571_);
                    v___x_4573_ = lean_array_get_size(v_modules_4572_);
                    v___x_4574_ = lean_nat_dec_lt(v_val_4570_, v___x_4573_);
                    if v___x_4574_ == 0 {
                        lean_dec_ref(v_modules_4572_);
                        lean_dec(v_val_4570_);
                        lean_dec_ref(v_env_4544_);
                        lean_dec(v_declName_4531_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4575_ = lean_st_ref_get(v___y_4537_);
                        v_env_4576_ = lean_ctor_get(v___x_4575_, 0);
                        lean_inc_ref(v_env_4576_);
                        lean_dec(v___x_4575_);
                        v___x_4577_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__2);
                        v___x_4578_ = lean_array_fget(v_modules_4572_, v_val_4570_);
                        lean_dec(v_val_4570_);
                        lean_dec_ref(v_modules_4572_);
                        if v_isMeta_4532_ == 0 {
                            lean_dec_ref(v_env_4576_);
                            v___y_4580_ = v_isMeta_4532_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_declName_4531_);
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
                v___x_4541_ = lean_box(0);
                v___x_4542_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4542_, 0, v___x_4541_);
                lean_ctor_set(v___x_4542_, 1, v___y_4533_);
                v___x_4543_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4543_, 0, v___x_4542_);
                return v___x_4543_;
            }
            2 => {
                v___x_4548_ = lean_box(0);
                v_sz_4549_ = lean_array_size(v___y_4547_);
                v___x_4550_ = 0usize;
                v___x_4551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__4(v_env_4544_, v_declName_4531_, v___y_4547_, v_sz_4549_, v___x_4550_, v___x_4548_, v___y_4546_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
                lean_dec_ref(v___y_4547_);
                lean_dec_ref(v_env_4544_);
                if lean_obj_tag(v___x_4551_) == 0 {
                    v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
                    v_isSharedCheck_4568_ = (!lean_is_exclusive(v___x_4551_)) as u8;
                    if v_isSharedCheck_4568_ == 0 {
                        v___x_4554_ = v___x_4551_;
                        v_isShared_4555_ = v_isSharedCheck_4568_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4552_);
                        lean_dec(v___x_4551_);
                        v___x_4554_ = lean_box(0);
                        v_isShared_4555_ = v_isSharedCheck_4568_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4551_;
                }
            }
            3 => {
                v_snd_4556_ = lean_ctor_get(v_a_4552_, 1);
                v_isSharedCheck_4566_ = (!lean_is_exclusive(v_a_4552_)) as u8;
                if v_isSharedCheck_4566_ == 0 {
                    v_unused_4567_ = lean_ctor_get(v_a_4552_, 0);
                    lean_dec(v_unused_4567_);
                    v___x_4558_ = v_a_4552_;
                    v_isShared_4559_ = v_isSharedCheck_4566_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_4556_);
                    lean_dec(v_a_4552_);
                    v___x_4558_ = lean_box(0);
                    v_isShared_4559_ = v_isSharedCheck_4566_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4559_ == 0 {
                    lean_ctor_set(v___x_4558_, 0, v___x_4548_);
                    v___x_4561_ = v___x_4558_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4548_);
                    lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_snd_4556_);
                    v___x_4561_ = v_reuseFailAlloc_4565_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4555_ == 0 {
                    lean_ctor_set(v___x_4554_, 0, v___x_4561_);
                    v___x_4563_ = v___x_4554_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
                    v___x_4563_ = v_reuseFailAlloc_4564_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4563_;
            }
            7 => {
                v_toImport_4581_ = lean_ctor_get(v___x_4578_, 0);
                lean_inc_ref(v_toImport_4581_);
                lean_dec(v___x_4578_);
                v_module_4582_ = lean_ctor_get(v_toImport_4581_, 0);
                lean_inc(v_module_4582_);
                lean_dec_ref(v_toImport_4581_);
                lean_inc(v_declName_4531_);
                v___x_4583_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3(v_module_4582_, v___y_4580_, v_declName_4531_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
                if lean_obj_tag(v___x_4583_) == 0 {
                    v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
                    lean_inc(v_a_4584_);
                    lean_dec_ref_known(v___x_4583_, 1);
                    v_snd_4585_ = lean_ctor_get(v_a_4584_, 1);
                    lean_inc(v_snd_4585_);
                    lean_dec(v_a_4584_);
                    v___x_4586_ = l_Lean_indirectModUseExt;
                    v___x_4587_ = lean_box(1);
                    v___x_4588_ = lean_box(0);
                    lean_inc_ref(v_env_4544_);
                    v___x_4589_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4577_,
                        v___x_4586_,
                        v_env_4544_,
                        v___x_4587_,
                        v___x_4588_,
                    );
                    v___x_4590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v___x_4589_, v_declName_4531_);
                    lean_dec(v___x_4589_);
                    if lean_obj_tag(v___x_4590_) == 0 {
                        v___x_4591_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__3;
                        v___y_4546_ = v_snd_4585_;
                        v___y_4547_ = v___x_4591_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4592_ = lean_ctor_get(v___x_4590_, 0);
                        lean_inc(v_val_4592_);
                        lean_dec_ref_known(v___x_4590_, 1);
                        v___y_4546_ = v_snd_4585_;
                        v___y_4547_ = v_val_4592_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_4544_);
                    lean_dec(v_declName_4531_);
                    return v___x_4583_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed(
    mut v_declName_4595_: *mut LeanObject,
    mut v_isMeta_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
    mut v___y_4600_: *mut LeanObject,
    mut v___y_4601_: *mut LeanObject,
    mut v___y_4602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_4603_: u8 = 0;
    let mut v_res_4604_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4603_ = (lean_unbox(v_isMeta_4596_) as u8);
    v_res_4604_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2(v_declName_4595_, v_isMeta_boxed_4603_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
    lean_dec(v___y_4601_);
    lean_dec_ref(v___y_4600_);
    lean_dec(v___y_4599_);
    lean_dec_ref(v___y_4598_);
    return v_res_4604_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(
    mut v_keys_4605_: *mut LeanObject,
    mut v_vals_4606_: *mut LeanObject,
    mut v_i_4607_: *mut LeanObject,
    mut v_k_4608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: u8 = 0;
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4609_ = lean_array_get_size(v_keys_4605_);
                v___x_4610_ = lean_nat_dec_lt(v_i_4607_, v___x_4609_);
                if v___x_4610_ == 0 {
                    lean_dec(v_i_4607_);
                    v___x_4611_ = lean_box(0);
                    return v___x_4611_;
                } else {
                    v_k_x27_4612_ = lean_array_fget_borrowed(v_keys_4605_, v_i_4607_);
                    v___x_4613_ = lean_name_eq(v_k_4608_, v_k_x27_4612_);
                    if v___x_4613_ == 0 {
                        v___x_4614_ = lean_unsigned_to_nat(1);
                        v___x_4615_ = lean_nat_add(v_i_4607_, v___x_4614_);
                        lean_dec(v_i_4607_);
                        v_i_4607_ = v___x_4615_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4617_ = lean_array_fget_borrowed(v_vals_4606_, v_i_4607_);
                        lean_dec(v_i_4607_);
                        lean_inc(v___x_4617_);
                        v___x_4618_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4618_, 0, v___x_4617_);
                        return v___x_4618_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_keys_4619_: *mut LeanObject,
    mut v_vals_4620_: *mut LeanObject,
    mut v_i_4621_: *mut LeanObject,
    mut v_k_4622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4623_: *mut LeanObject = core::ptr::null_mut();
    v_res_4623_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_4619_, v_vals_4620_, v_i_4621_, v_k_4622_);
    lean_dec(v_k_4622_);
    lean_dec_ref(v_vals_4620_);
    lean_dec_ref(v_keys_4619_);
    return v_res_4623_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(
    mut v_x_4624_: *mut LeanObject,
    mut v_x_4625_: usize,
    mut v_x_4626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: usize = 0;
    let mut v___x_4630_: usize = 0;
    let mut v___x_4631_: usize = 0;
    let mut v_j_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: u8 = 0;
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: usize = 0;
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4624_) == 0 {
                    v_es_4627_ = lean_ctor_get(v_x_4624_, 0);
                    v___x_4628_ = lean_box(2);
                    v___x_4629_ = 5usize;
                    v___x_4630_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg___closed__1);
                    v___x_4631_ = lean_usize_land(v_x_4625_, v___x_4630_);
                    v_j_4632_ = lean_usize_to_nat(v___x_4631_);
                    v___x_4633_ = lean_array_get_borrowed(v___x_4628_, v_es_4627_, v_j_4632_);
                    lean_dec(v_j_4632_);
                    match lean_obj_tag(v___x_4633_) {
                        0 => {
                            v_key_4634_ = lean_ctor_get(v___x_4633_, 0);
                            v_val_4635_ = lean_ctor_get(v___x_4633_, 1);
                            v___x_4636_ = lean_name_eq(v_x_4626_, v_key_4634_);
                            if v___x_4636_ == 0 {
                                v___x_4637_ = lean_box(0);
                                return v___x_4637_;
                            } else {
                                lean_inc(v_val_4635_);
                                v___x_4638_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4638_, 0, v_val_4635_);
                                return v___x_4638_;
                            }
                        }
                        1 => {
                            v_node_4639_ = lean_ctor_get(v___x_4633_, 0);
                            v___x_4640_ = lean_usize_shift_right(v_x_4625_, v___x_4629_);
                            v_x_4624_ = v_node_4639_;
                            v_x_4625_ = v___x_4640_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4642_ = lean_box(0);
                            return v___x_4642_;
                        }
                    }
                } else {
                    v_ks_4643_ = lean_ctor_get(v_x_4624_, 0);
                    v_vs_4644_ = lean_ctor_get(v_x_4624_, 1);
                    v___x_4645_ = lean_unsigned_to_nat(0);
                    v___x_4646_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_ks_4643_, v_vs_4644_, v___x_4645_, v_x_4626_);
                    return v___x_4646_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg___boxed(
    mut v_x_4647_: *mut LeanObject,
    mut v_x_4648_: *mut LeanObject,
    mut v_x_4649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30267__boxed_4650_: usize = 0;
    let mut v_res_4651_: *mut LeanObject = core::ptr::null_mut();
    v_x_30267__boxed_4650_ = lean_unbox_usize(v_x_4648_);
    lean_dec(v_x_4648_);
    v_res_4651_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_4647_, v_x_30267__boxed_4650_, v_x_4649_);
    lean_dec(v_x_4649_);
    lean_dec_ref(v_x_4647_);
    return v_res_4651_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(
    mut v_x_4652_: *mut LeanObject,
    mut v_x_4653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4655_: u64 = 0;
    let mut v___x_4656_: usize = 0;
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: u64 = 0;
    let mut v_hash_4659_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4653_) == 0 {
                    v___x_4658_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg___closed__0);
                    v___y_4655_ = v___x_4658_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4659_ = lean_ctor_get_uint64(
                        v_x_4653_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_x_4660_: *mut LeanObject,
    mut v_x_4661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4662_: *mut LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_4660_, v_x_4661_);
    lean_dec(v_x_4661_);
    lean_dec_ref(v_x_4660_);
    return v_res_4662_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    v___x_4663_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__1;
    v___x_4664_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___closed__0;
    v___x_4665_ =
        l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_4664_, v___x_4663_);
    return v___x_4665_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2()
-> *mut LeanObject {
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    v___x_4667_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__1;
    v___x_4668_ = l_Lean_stringToMessageData(v___x_4667_);
    return v___x_4668_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4()
-> *mut LeanObject {
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    v___x_4670_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__3;
    v___x_4671_ = l_Lean_stringToMessageData(v___x_4670_);
    return v___x_4671_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6()
-> *mut LeanObject {
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    v___x_4673_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__5;
    v___x_4674_ = l_Lean_stringToMessageData(v___x_4673_);
    return v___x_4674_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8()
-> *mut LeanObject {
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    v___x_4676_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__7;
    v___x_4677_ = l_Lean_stringToMessageData(v___x_4676_);
    return v___x_4677_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(
    mut v_origDecl_4678_: *mut LeanObject,
    mut v_init_4679_: *mut LeanObject,
    mut v_x_4680_: *mut LeanObject,
    mut v___y_4681_: *mut LeanObject,
    mut v___y_4682_: *mut LeanObject,
    mut v___y_4683_: *mut LeanObject,
    mut v___y_4684_: *mut LeanObject,
    mut v___y_4685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4695_: u8 = 0;
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: u8 = 0;
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4712_: u8 = 0;
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4721_: u8 = 0;
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4725_: u8 = 0;
    let mut v_toSignature_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: u8 = 0;
    let mut v___x_4729_: u8 = 0;
    let mut v_a_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4733_: u8 = 0;
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4768_: u8 = 0;
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut v_reuseFailAlloc_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: u8 = 0;
    let mut v_snd_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: u8 = 0;
    let mut v___y_4788_: u8 = 0;
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: u8 = 0;
    let mut v___x_4792_: u8 = 0;
    let mut v___x_4793_: u8 = 0;
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4803_: u8 = 0;
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: u8 = 0;
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExported_4812_: u8 = 0;
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_unused_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4680_) == 0 {
                    v_k_4687_ = lean_ctor_get(v_x_4680_, 1);
                    lean_inc(v_k_4687_);
                    v_l_4688_ = lean_ctor_get(v_x_4680_, 3);
                    lean_inc(v_l_4688_);
                    v_r_4689_ = lean_ctor_get(v_x_4680_, 4);
                    lean_inc(v_r_4689_);
                    lean_dec_ref_known(v_x_4680_, 5);
                    lean_inc_ref(v_origDecl_4678_);
                    v___x_4690_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_4678_, v_init_4679_, v_l_4688_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
                    if lean_obj_tag(v___x_4690_) == 0 {
                        v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
                        lean_inc(v_a_4691_);
                        lean_dec_ref_known(v___x_4690_, 1);
                        v_snd_4692_ = lean_ctor_get(v_a_4691_, 1);
                        v_isSharedCheck_4815_ = (!lean_is_exclusive(v_a_4691_)) as u8;
                        if v_isSharedCheck_4815_ == 0 {
                            v_unused_4816_ = lean_ctor_get(v_a_4691_, 0);
                            lean_dec(v_unused_4816_);
                            v___x_4694_ = v_a_4691_;
                            v_isShared_4695_ = v_isSharedCheck_4815_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_4692_);
                            lean_dec(v_a_4691_);
                            v___x_4694_ = lean_box(0);
                            v_isShared_4695_ = v_isSharedCheck_4815_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_r_4689_);
                        lean_dec(v_k_4687_);
                        lean_dec_ref(v_origDecl_4678_);
                        return v___x_4690_;
                    }
                } else {
                    lean_dec_ref(v_origDecl_4678_);
                    v___x_4817_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4817_, 0, v_init_4679_);
                    v___x_4818_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4818_, 0, v___x_4817_);
                    lean_ctor_set(v___x_4818_, 1, v___y_4681_);
                    v___x_4819_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4819_, 0, v___x_4818_);
                    return v___x_4819_;
                }
            }
            1 => {
                v___x_4696_ = lean_box(0);
                v___x_4697_ = l_Lean_NameSet_contains(v_snd_4692_, v_k_4687_);
                if v___x_4697_ == 0 {
                    v___x_4698_ = lean_st_ref_get(v___y_4685_);
                    v_env_4699_ = lean_ctor_get(v___x_4698_, 0);
                    lean_inc_ref(v_env_4699_);
                    lean_dec(v___x_4698_);
                    v___x_4700_ = l_Lean_Compiler_LCNF_baseExt;
                    v_toEnvExtension_4701_ = lean_ctor_get(v___x_4700_, 0);
                    v_asyncMode_4702_ = lean_ctor_get(v_toEnvExtension_4701_, 2);
                    lean_inc(v_k_4687_);
                    v___x_4703_ = l_Lean_NameSet_insert(v_snd_4692_, v_k_4687_);
                    v___x_4704_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__0);
                    v___x_4705_ = lean_box(0);
                    v___x_4706_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_4704_,
                        v___x_4700_,
                        v_env_4699_,
                        v_asyncMode_4702_,
                        v___x_4705_,
                    );
                    v___x_4707_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v___x_4706_, v_k_4687_);
                    lean_dec(v___x_4706_);
                    if lean_obj_tag(v___x_4707_) == 1 {
                        lean_del_object(v___x_4694_);
                        lean_dec(v_k_4687_);
                        v_val_4708_ = lean_ctor_get(v___x_4707_, 0);
                        lean_inc_n(v_val_4708_, 2);
                        lean_dec_ref_known(v___x_4707_, 1);
                        v___x_4709_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(
                            v_val_4708_,
                            v___y_4684_,
                            v___y_4685_,
                        );
                        if lean_obj_tag(v___x_4709_) == 0 {
                            v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
                            lean_inc(v_a_4710_);
                            lean_dec_ref_known(v___x_4709_, 1);
                            v_toSignature_4726_ = lean_ctor_get(v_val_4708_, 0);
                            v_name_4727_ = lean_ctor_get(v_toSignature_4726_, 0);
                            v___x_4728_ = l_Lean_isPrivateName(v_name_4727_);
                            if v___x_4728_ == 0 {
                                lean_dec(v_a_4710_);
                                v___y_4712_ = v___x_4728_;
                                state = 2;
                                continue;
                            } else {
                                v___x_4729_ = (lean_unbox(v_a_4710_) as u8);
                                lean_dec(v_a_4710_);
                                v___y_4712_ = v___x_4729_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_4708_);
                            lean_dec(v___x_4703_);
                            lean_dec(v_r_4689_);
                            lean_dec_ref(v_origDecl_4678_);
                            v_a_4730_ = lean_ctor_get(v___x_4709_, 0);
                            v_isSharedCheck_4737_ = (!lean_is_exclusive(v___x_4709_)) as u8;
                            if v_isSharedCheck_4737_ == 0 {
                                v___x_4732_ = v___x_4709_;
                                v_isShared_4733_ = v_isSharedCheck_4737_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4730_);
                                lean_dec(v___x_4709_);
                                v___x_4732_ = lean_box(0);
                                v_isShared_4733_ = v_isSharedCheck_4737_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4707_);
                        v___x_4738_ = lean_st_ref_get(v___y_4685_);
                        v_env_4739_ = lean_ctor_get(v___x_4738_, 0);
                        lean_inc_ref(v_env_4739_);
                        lean_dec(v___x_4738_);
                        v___x_4740_ =
                            l_Lean_Environment_getModuleIdxFor_x3f(v_env_4739_, v_k_4687_);
                        lean_dec_ref(v_env_4739_);
                        if lean_obj_tag(v___x_4740_) == 1 {
                            v_val_4741_ = lean_ctor_get(v___x_4740_, 0);
                            lean_inc(v_val_4741_);
                            lean_dec_ref_known(v___x_4740_, 1);
                            v___x_4774_ = lean_st_ref_get(v___y_4685_);
                            v_env_4783_ = lean_ctor_get(v___x_4774_, 0);
                            lean_inc_ref(v_env_4783_);
                            lean_dec(v___x_4774_);
                            v___x_4784_ = l_Lean_Environment_header(v_env_4783_);
                            lean_dec_ref(v_env_4783_);
                            v_modules_4785_ = lean_ctor_get(v___x_4784_, 3);
                            lean_inc_ref(v_modules_4785_);
                            lean_dec_ref(v___x_4784_);
                            v___x_4786_ = 1;
                            v___x_4808_ = lean_array_get_size(v_modules_4785_);
                            v___x_4809_ = lean_nat_dec_lt(v_val_4741_, v___x_4808_);
                            if v___x_4809_ == 0 {
                                lean_dec_ref(v_modules_4785_);
                                v___y_4788_ = v___x_4697_;
                                state = 12;
                                continue;
                            } else {
                                v___x_4810_ = lean_array_fget(v_modules_4785_, v_val_4741_);
                                lean_dec_ref(v_modules_4785_);
                                v_toImport_4811_ = lean_ctor_get(v___x_4810_, 0);
                                lean_inc_ref(v_toImport_4811_);
                                lean_dec(v___x_4810_);
                                v_isExported_4812_ = lean_ctor_get_uint8(
                                    v_toImport_4811_,
                                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                );
                                lean_dec_ref(v_toImport_4811_);
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
                            lean_dec(v___x_4740_);
                            lean_del_object(v___x_4694_);
                            lean_dec(v_k_4687_);
                            v_init_4679_ = v___x_4696_;
                            v_x_4680_ = v_r_4689_;
                            v___y_4681_ = v___x_4703_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4694_);
                    lean_dec(v_k_4687_);
                    v_init_4679_ = v___x_4696_;
                    v_x_4680_ = v_r_4689_;
                    v___y_4681_ = v_snd_4692_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_4712_ == 0 {
                    lean_dec(v_val_4708_);
                    v_init_4679_ = v___x_4696_;
                    v_x_4680_ = v_r_4689_;
                    v___y_4681_ = v___x_4703_;
                    state = 0;
                    continue;
                } else {
                    lean_inc_ref(v_origDecl_4678_);
                    v___x_4714_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_origDecl_4678_, v_val_4708_, v___x_4703_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
                    if lean_obj_tag(v___x_4714_) == 0 {
                        v_a_4715_ = lean_ctor_get(v___x_4714_, 0);
                        lean_inc(v_a_4715_);
                        lean_dec_ref_known(v___x_4714_, 1);
                        v_snd_4716_ = lean_ctor_get(v_a_4715_, 1);
                        lean_inc(v_snd_4716_);
                        lean_dec(v_a_4715_);
                        v_init_4679_ = v___x_4696_;
                        v_x_4680_ = v_r_4689_;
                        v___y_4681_ = v_snd_4716_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_r_4689_);
                        lean_dec_ref(v_origDecl_4678_);
                        v_a_4718_ = lean_ctor_get(v___x_4714_, 0);
                        v_isSharedCheck_4725_ = (!lean_is_exclusive(v___x_4714_)) as u8;
                        if v_isSharedCheck_4725_ == 0 {
                            v___x_4720_ = v___x_4714_;
                            v_isShared_4721_ = v_isSharedCheck_4725_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4718_);
                            lean_dec(v___x_4714_);
                            v___x_4720_ = lean_box(0);
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
                    v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
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
                    v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
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
                v_toSignature_4744_ = lean_ctor_get(v_origDecl_4678_, 0);
                lean_inc_ref(v_toSignature_4744_);
                lean_dec_ref(v_origDecl_4678_);
                v_env_4745_ = lean_ctor_get(v___x_4743_, 0);
                lean_inc_ref(v_env_4745_);
                lean_dec(v___x_4743_);
                v_name_4746_ = lean_ctor_get(v_toSignature_4744_, 0);
                lean_inc(v_name_4746_);
                lean_dec_ref(v_toSignature_4744_);
                v___x_4747_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__2);
                v___x_4748_ = l_Lean_MessageData_ofConstName(v_name_4746_, v___x_4697_);
                if v_isShared_4695_ == 0 {
                    lean_ctor_set_tag(v___x_4694_, 7);
                    lean_ctor_set(v___x_4694_, 1, v___x_4748_);
                    lean_ctor_set(v___x_4694_, 0, v___x_4747_);
                    v___x_4750_ = v___x_4694_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4773_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4747_);
                    lean_ctor_set(v_reuseFailAlloc_4773_, 1, v___x_4748_);
                    v___x_4750_ = v_reuseFailAlloc_4773_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4751_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__4);
                v___x_4752_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4752_, 0, v___x_4750_);
                lean_ctor_set(v___x_4752_, 1, v___x_4751_);
                v___x_4753_ = l_Lean_MessageData_ofConstName(v_k_4687_, v___x_4697_);
                v___x_4754_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4754_, 0, v___x_4752_);
                lean_ctor_set(v___x_4754_, 1, v___x_4753_);
                v___x_4755_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__6);
                v___x_4756_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4756_, 0, v___x_4754_);
                lean_ctor_set(v___x_4756_, 1, v___x_4755_);
                v___x_4757_ = l_Lean_Environment_header(v_env_4745_);
                lean_dec_ref(v_env_4745_);
                v___x_4758_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4757_);
                v___x_4759_ = lean_array_get(v___x_4705_, v___x_4758_, v_val_4741_);
                lean_dec(v_val_4741_);
                lean_dec_ref(v___x_4758_);
                v___x_4760_ = l_Lean_MessageData_ofName(v___x_4759_);
                v___x_4761_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4761_, 0, v___x_4756_);
                lean_ctor_set(v___x_4761_, 1, v___x_4760_);
                v___x_4762_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___closed__8);
                v___x_4763_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4763_, 0, v___x_4761_);
                lean_ctor_set(v___x_4763_, 1, v___x_4762_);
                v___x_4764_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__0___redArg(v___x_4763_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
                v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
                v_isSharedCheck_4772_ = (!lean_is_exclusive(v___x_4764_)) as u8;
                if v_isSharedCheck_4772_ == 0 {
                    v___x_4767_ = v___x_4764_;
                    v_isShared_4768_ = v_isSharedCheck_4772_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_a_4765_);
                    lean_dec(v___x_4764_);
                    v___x_4767_ = lean_box(0);
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
                    v_reuseFailAlloc_4771_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
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
                v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
                lean_inc(v_a_4778_);
                lean_dec_ref(v___x_4777_);
                v_fst_4779_ = lean_ctor_get(v_a_4778_, 0);
                v___x_4780_ = (lean_unbox(v_fst_4779_) as u8);
                if v___x_4780_ == 0 {
                    lean_dec(v_a_4778_);
                    lean_dec(v_r_4689_);
                    state = 7;
                    continue;
                } else {
                    if v___x_4697_ == 0 {
                        lean_dec(v_val_4741_);
                        lean_del_object(v___x_4694_);
                        lean_dec(v_k_4687_);
                        v_snd_4781_ = lean_ctor_get(v_a_4778_, 1);
                        lean_inc(v_snd_4781_);
                        lean_dec(v_a_4778_);
                        v_init_4679_ = v___x_4696_;
                        v_x_4680_ = v_r_4689_;
                        v___y_4681_ = v_snd_4781_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_4778_);
                        lean_dec(v_r_4689_);
                        state = 7;
                        continue;
                    }
                }
            }
            12 => {
                if v___y_4788_ == 0 {
                    lean_dec(v_val_4741_);
                    lean_del_object(v___x_4694_);
                    v___x_4789_ = lean_st_ref_get(v___y_4685_);
                    v_env_4790_ = lean_ctor_get(v___x_4789_, 0);
                    lean_inc_ref(v_env_4790_);
                    lean_dec(v___x_4789_);
                    lean_inc(v_k_4687_);
                    v___x_4791_ = l_Lean_getIRPhases(v_env_4790_, v_k_4687_);
                    v___x_4792_ = 1;
                    v___x_4793_ = l_Lean_instBEqIRPhases_beq(v___x_4791_, v___x_4792_);
                    v___x_4794_ = lean_box((v___x_4793_) as usize);
                    v___x_4795_ = lean_alloc_closure(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2___boxed as *mut core::ffi::c_void, 8, 2);
                    lean_closure_set(v___x_4795_, 0, v_k_4687_);
                    lean_closure_set(v___x_4795_, 1, v___x_4794_);
                    v___x_4796_ = l_Lean_withExporting___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__3___redArg(v___x_4795_, v___x_4786_, v___x_4703_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
                    if lean_obj_tag(v___x_4796_) == 0 {
                        v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
                        lean_inc(v_a_4797_);
                        lean_dec_ref_known(v___x_4796_, 1);
                        v_snd_4798_ = lean_ctor_get(v_a_4797_, 1);
                        lean_inc(v_snd_4798_);
                        lean_dec(v_a_4797_);
                        v_init_4679_ = v___x_4696_;
                        v_x_4680_ = v_r_4689_;
                        v___y_4681_ = v_snd_4798_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_r_4689_);
                        lean_dec_ref(v_origDecl_4678_);
                        v_a_4800_ = lean_ctor_get(v___x_4796_, 0);
                        v_isSharedCheck_4807_ = (!lean_is_exclusive(v___x_4796_)) as u8;
                        if v_isSharedCheck_4807_ == 0 {
                            v___x_4802_ = v___x_4796_;
                            v_isShared_4803_ = v_isSharedCheck_4807_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4800_);
                            lean_dec(v___x_4796_);
                            v___x_4802_ = lean_box(0);
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
                    v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
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
    mut v_origDecl_4821_: *mut LeanObject,
    mut v_code_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
    mut v___y_4824_: *mut LeanObject,
    mut v___y_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
    mut v___y_4827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v_snd_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4840_: u8 = 0;
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4847_: u8 = 0;
    let mut v_unused_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut v_a_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4853_: u8 = 0;
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4829_ = l_Lean_NameSet_empty;
                v___x_4830_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_collectUsedDecls(v___x_4820_, v_code_4822_, v___x_4829_);
                v___x_4831_ = lean_box(0);
                v___x_4832_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_4821_, v___x_4831_, v___x_4830_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
                if lean_obj_tag(v___x_4832_) == 0 {
                    v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
                    v_isSharedCheck_4849_ = (!lean_is_exclusive(v___x_4832_)) as u8;
                    if v_isSharedCheck_4849_ == 0 {
                        v___x_4835_ = v___x_4832_;
                        v_isShared_4836_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4833_);
                        lean_dec(v___x_4832_);
                        v___x_4835_ = lean_box(0);
                        v_isShared_4836_ = v_isSharedCheck_4849_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4850_ = lean_ctor_get(v___x_4832_, 0);
                    v_isSharedCheck_4857_ = (!lean_is_exclusive(v___x_4832_)) as u8;
                    if v_isSharedCheck_4857_ == 0 {
                        v___x_4852_ = v___x_4832_;
                        v_isShared_4853_ = v_isSharedCheck_4857_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4850_);
                        lean_dec(v___x_4832_);
                        v___x_4852_ = lean_box(0);
                        v_isShared_4853_ = v_isSharedCheck_4857_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4837_ = lean_ctor_get(v_a_4833_, 1);
                v_isSharedCheck_4847_ = (!lean_is_exclusive(v_a_4833_)) as u8;
                if v_isSharedCheck_4847_ == 0 {
                    v_unused_4848_ = lean_ctor_get(v_a_4833_, 0);
                    lean_dec(v_unused_4848_);
                    v___x_4839_ = v_a_4833_;
                    v_isShared_4840_ = v_isSharedCheck_4847_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4837_);
                    lean_dec(v_a_4833_);
                    v___x_4839_ = lean_box(0);
                    v_isShared_4840_ = v_isSharedCheck_4847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4840_ == 0 {
                    lean_ctor_set(v___x_4839_, 0, v___x_4831_);
                    v___x_4842_ = v___x_4839_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4831_);
                    lean_ctor_set(v_reuseFailAlloc_4846_, 1, v_snd_4837_);
                    v___x_4842_ = v_reuseFailAlloc_4846_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4836_ == 0 {
                    lean_ctor_set(v___x_4835_, 0, v___x_4842_);
                    v___x_4844_ = v___x_4835_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4842_);
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
                    v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
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
    mut v___x_4858_: *mut LeanObject,
    mut v_origDecl_4859_: *mut LeanObject,
    mut v_code_4860_: *mut LeanObject,
    mut v___y_4861_: *mut LeanObject,
    mut v___y_4862_: *mut LeanObject,
    mut v___y_4863_: *mut LeanObject,
    mut v___y_4864_: *mut LeanObject,
    mut v___y_4865_: *mut LeanObject,
    mut v___y_4866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_30356__boxed_4867_: u8 = 0;
    let mut v_res_4868_: *mut LeanObject = core::ptr::null_mut();
    v___x_30356__boxed_4867_ = (lean_unbox(v___x_4858_) as u8);
    v_res_4868_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0(v___x_30356__boxed_4867_, v_origDecl_4859_, v_code_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
    lean_dec(v___y_4865_);
    lean_dec_ref(v___y_4864_);
    lean_dec(v___y_4863_);
    lean_dec_ref(v___y_4862_);
    return v_res_4868_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(
    mut v_origDecl_4869_: *mut LeanObject,
    mut v_decl_4870_: *mut LeanObject,
    mut v_a_4871_: *mut LeanObject,
    mut v_a_4872_: *mut LeanObject,
    mut v_a_4873_: *mut LeanObject,
    mut v_a_4874_: *mut LeanObject,
    mut v_a_4875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: u8 = 0;
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    v_value_4877_ = lean_ctor_get(v_decl_4870_, 1);
    lean_inc_ref(v_value_4877_);
    lean_dec_ref(v_decl_4870_);
    v___x_4878_ = 0;
    v___x_4879_ = lean_box((v___x_4878_) as usize);
    v___f_4880_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
    lean_closure_set(v___f_4880_, 0, v___x_4879_);
    lean_closure_set(v___f_4880_, 1, v_origDecl_4869_);
    v___x_4881_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkMeta_go_spec__3___redArg(v___f_4880_, v_value_4877_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
    return v___x_4881_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go___boxed(
    mut v_origDecl_4882_: *mut LeanObject,
    mut v_decl_4883_: *mut LeanObject,
    mut v_a_4884_: *mut LeanObject,
    mut v_a_4885_: *mut LeanObject,
    mut v_a_4886_: *mut LeanObject,
    mut v_a_4887_: *mut LeanObject,
    mut v_a_4888_: *mut LeanObject,
    mut v_a_4889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4890_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4888_);
    lean_dec_ref(v_a_4887_);
    lean_dec(v_a_4886_);
    lean_dec_ref(v_a_4885_);
    return v_res_4890_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4___boxed(
    mut v_origDecl_4891_: *mut LeanObject,
    mut v_init_4892_: *mut LeanObject,
    mut v_x_4893_: *mut LeanObject,
    mut v___y_4894_: *mut LeanObject,
    mut v___y_4895_: *mut LeanObject,
    mut v___y_4896_: *mut LeanObject,
    mut v___y_4897_: *mut LeanObject,
    mut v___y_4898_: *mut LeanObject,
    mut v___y_4899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4900_: *mut LeanObject = core::ptr::null_mut();
    v_res_4900_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__4(v_origDecl_4891_, v_init_4892_, v_x_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
    lean_dec(v___y_4898_);
    lean_dec_ref(v___y_4897_);
    lean_dec(v___y_4896_);
    lean_dec_ref(v___y_4895_);
    return v_res_4900_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(
    mut v_00_u03b2_4901_: *mut LeanObject,
    mut v_x_4902_: *mut LeanObject,
    mut v_x_4903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    v___x_4904_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___redArg(v_x_4902_, v_x_4903_);
    return v___x_4904_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0___boxed(
    mut v_00_u03b2_4905_: *mut LeanObject,
    mut v_x_4906_: *mut LeanObject,
    mut v_x_4907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4908_: *mut LeanObject = core::ptr::null_mut();
    v_res_4908_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0(v_00_u03b2_4905_, v_x_4906_, v_x_4907_);
    lean_dec(v_x_4907_);
    lean_dec_ref(v_x_4906_);
    return v_res_4908_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(
    mut v_opt_4909_: *mut LeanObject,
    mut v___y_4910_: *mut LeanObject,
    mut v___y_4911_: *mut LeanObject,
    mut v___y_4912_: *mut LeanObject,
    mut v___y_4913_: *mut LeanObject,
    mut v___y_4914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    v___x_4916_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___redArg(v_opt_4909_, v___y_4910_, v___y_4913_);
    return v___x_4916_;
}
pub unsafe fn l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1___boxed(
    mut v_opt_4917_: *mut LeanObject,
    mut v___y_4918_: *mut LeanObject,
    mut v___y_4919_: *mut LeanObject,
    mut v___y_4920_: *mut LeanObject,
    mut v___y_4921_: *mut LeanObject,
    mut v___y_4922_: *mut LeanObject,
    mut v___y_4923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4924_: *mut LeanObject = core::ptr::null_mut();
    v_res_4924_ = l_Lean_Option_getM___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__1(v_opt_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_);
    lean_dec(v___y_4922_);
    lean_dec_ref(v___y_4921_);
    lean_dec(v___y_4920_);
    lean_dec_ref(v___y_4919_);
    lean_dec_ref(v_opt_4917_);
    return v_res_4924_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(
    mut v_00_u03b2_4925_: *mut LeanObject,
    mut v_x_4926_: *mut LeanObject,
    mut v_x_4927_: usize,
    mut v_x_4928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    v___x_4929_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___redArg(v_x_4926_, v_x_4927_, v_x_4928_);
    return v___x_4929_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_4930_: *mut LeanObject,
    mut v_x_4931_: *mut LeanObject,
    mut v_x_4932_: *mut LeanObject,
    mut v_x_4933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30773__boxed_4934_: usize = 0;
    let mut v_res_4935_: *mut LeanObject = core::ptr::null_mut();
    v_x_30773__boxed_4934_ = lean_unbox_usize(v_x_4932_);
    lean_dec(v_x_4932_);
    v_res_4935_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0(v_00_u03b2_4930_, v_x_4931_, v_x_30773__boxed_4934_, v_x_4933_);
    lean_dec(v_x_4933_);
    lean_dec_ref(v_x_4931_);
    return v_res_4935_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(
    mut v_00_u03b2_4936_: *mut LeanObject,
    mut v_m_4937_: *mut LeanObject,
    mut v_a_4938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    v___x_4939_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___redArg(v_m_4937_, v_a_4938_);
    return v___x_4939_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5___boxed(
    mut v_00_u03b2_4940_: *mut LeanObject,
    mut v_m_4941_: *mut LeanObject,
    mut v_a_4942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4943_: *mut LeanObject = core::ptr::null_mut();
    v_res_4943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5(v_00_u03b2_4940_, v_m_4941_, v_a_4942_);
    lean_dec(v_a_4942_);
    lean_dec_ref(v_m_4941_);
    return v_res_4943_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4944_: *mut LeanObject,
    mut v_keys_4945_: *mut LeanObject,
    mut v_vals_4946_: *mut LeanObject,
    mut v_heq_4947_: *mut LeanObject,
    mut v_i_4948_: *mut LeanObject,
    mut v_k_4949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    v___x_4950_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___redArg(v_keys_4945_, v_vals_4946_, v_i_4948_, v_k_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_4951_: *mut LeanObject,
    mut v_keys_4952_: *mut LeanObject,
    mut v_vals_4953_: *mut LeanObject,
    mut v_heq_4954_: *mut LeanObject,
    mut v_i_4955_: *mut LeanObject,
    mut v_k_4956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4957_: *mut LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__0_spec__0_spec__2(v_00_u03b2_4951_, v_keys_4952_, v_vals_4953_, v_heq_4954_, v_i_4955_, v_k_4956_);
    lean_dec(v_k_4956_);
    lean_dec_ref(v_vals_4953_);
    lean_dec_ref(v_keys_4952_);
    return v_res_4957_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(
    mut v_00_u03b2_4958_: *mut LeanObject,
    mut v_x_4959_: *mut LeanObject,
    mut v_x_4960_: *mut LeanObject,
) -> u8 {
    let mut v___x_4961_: u8 = 0;
    v___x_4961_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___redArg(v_x_4959_, v_x_4960_);
    return v___x_4961_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b2_4962_: *mut LeanObject,
    mut v_x_4963_: *mut LeanObject,
    mut v_x_4964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4965_: u8 = 0;
    let mut v_r_4966_: *mut LeanObject = core::ptr::null_mut();
    v_res_4965_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6(v_00_u03b2_4962_, v_x_4963_, v_x_4964_);
    lean_dec_ref(v_x_4964_);
    lean_dec_ref(v_x_4963_);
    v_r_4966_ = lean_box((v_res_4965_) as usize);
    return v_r_4966_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(
    mut v_00_u03b2_4967_: *mut LeanObject,
    mut v_a_4968_: *mut LeanObject,
    mut v_x_4969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    v___x_4970_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___redArg(v_a_4968_, v_x_4969_);
    return v___x_4970_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10___boxed(
    mut v_00_u03b2_4971_: *mut LeanObject,
    mut v_a_4972_: *mut LeanObject,
    mut v_x_4973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4974_: *mut LeanObject = core::ptr::null_mut();
    v_res_4974_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__5_spec__10(v_00_u03b2_4971_, v_a_4972_, v_x_4973_);
    lean_dec(v_x_4973_);
    lean_dec(v_a_4972_);
    return v_res_4974_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(
    mut v_00_u03b2_4975_: *mut LeanObject,
    mut v_x_4976_: *mut LeanObject,
    mut v_x_4977_: usize,
    mut v_x_4978_: *mut LeanObject,
) -> u8 {
    let mut v___x_4979_: u8 = 0;
    v___x_4979_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___redArg(v_x_4976_, v_x_4977_, v_x_4978_);
    return v___x_4979_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8___boxed(
    mut v_00_u03b2_4980_: *mut LeanObject,
    mut v_x_4981_: *mut LeanObject,
    mut v_x_4982_: *mut LeanObject,
    mut v_x_4983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30801__boxed_4984_: usize = 0;
    let mut v_res_4985_: u8 = 0;
    let mut v_r_4986_: *mut LeanObject = core::ptr::null_mut();
    v_x_30801__boxed_4984_ = lean_unbox_usize(v_x_4982_);
    lean_dec(v_x_4982_);
    v_res_4985_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_4980_, v_x_4981_, v_x_30801__boxed_4984_, v_x_4983_);
    lean_dec_ref(v_x_4983_);
    lean_dec_ref(v_x_4981_);
    v_r_4986_ = lean_box((v_res_4985_) as usize);
    return v_r_4986_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(
    mut v_00_u03b2_4987_: *mut LeanObject,
    mut v_keys_4988_: *mut LeanObject,
    mut v_vals_4989_: *mut LeanObject,
    mut v_heq_4990_: *mut LeanObject,
    mut v_i_4991_: *mut LeanObject,
    mut v_k_4992_: *mut LeanObject,
) -> u8 {
    let mut v___x_4993_: u8 = 0;
    v___x_4993_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___redArg(v_keys_4988_, v_i_4991_, v_k_4992_);
    return v___x_4993_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12___boxed(
    mut v_00_u03b2_4994_: *mut LeanObject,
    mut v_keys_4995_: *mut LeanObject,
    mut v_vals_4996_: *mut LeanObject,
    mut v_heq_4997_: *mut LeanObject,
    mut v_i_4998_: *mut LeanObject,
    mut v_k_4999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5000_: u8 = 0;
    let mut v_r_5001_: *mut LeanObject = core::ptr::null_mut();
    v_res_5000_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go_spec__2_spec__3_spec__6_spec__8_spec__12(v_00_u03b2_4994_, v_keys_4995_, v_vals_4996_, v_heq_4997_, v_i_4998_, v_k_4999_);
    lean_dec_ref(v_k_4999_);
    lean_dec_ref(v_vals_4996_);
    lean_dec_ref(v_keys_4995_);
    v_r_5001_ = lean_box((v_res_5000_) as usize);
    return v_r_5001_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(
    mut v_as_5002_: *mut LeanObject,
    mut v_sz_5003_: usize,
    mut v_i_5004_: usize,
    mut v_b_5005_: *mut LeanObject,
    mut v___y_5006_: *mut LeanObject,
    mut v___y_5007_: *mut LeanObject,
    mut v___y_5008_: *mut LeanObject,
    mut v___y_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: usize = 0;
    let mut v___x_5014_: usize = 0;
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: u8 = 0;
    let mut v___x_5025_: u8 = 0;
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5032_: u8 = 0;
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_a_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5016_ = lean_usize_dec_lt(v_i_5004_, v_sz_5003_);
                if v___x_5016_ == 0 {
                    v___x_5017_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5017_, 0, v_b_5005_);
                    return v___x_5017_;
                } else {
                    v_a_5018_ = lean_array_uget_borrowed(v_as_5002_, v_i_5004_);
                    lean_inc(v_a_5018_);
                    v___x_5019_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(
                        v_a_5018_,
                        v___y_5008_,
                        v___y_5009_,
                    );
                    if lean_obj_tag(v___x_5019_) == 0 {
                        v_toSignature_5020_ = lean_ctor_get(v_a_5018_, 0);
                        v_a_5021_ = lean_ctor_get(v___x_5019_, 0);
                        lean_inc(v_a_5021_);
                        lean_dec_ref_known(v___x_5019_, 1);
                        v_name_5022_ = lean_ctor_get(v_toSignature_5020_, 0);
                        v___x_5023_ = lean_box(0);
                        v___x_5024_ = l_Lean_isPrivateName(v_name_5022_);
                        if v___x_5024_ == 0 {
                            v___x_5025_ = (lean_unbox(v_a_5021_) as u8);
                            lean_dec(v_a_5021_);
                            if v___x_5025_ == 0 {
                                v_a_5012_ = v___x_5023_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5026_ = lean_st_ref_get(v___y_5009_);
                                lean_dec(v___x_5026_);
                                v___x_5027_ = l_Lean_NameSet_empty;
                                lean_inc_n(v_a_5018_, 2);
                                v___x_5028_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_checkTemplateVisibility_go(v_a_5018_, v_a_5018_, v___x_5027_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
                                if lean_obj_tag(v___x_5028_) == 0 {
                                    lean_dec_ref_known(v___x_5028_, 1);
                                    v_a_5012_ = v___x_5023_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
                                    v_isSharedCheck_5036_ = (!lean_is_exclusive(v___x_5028_)) as u8;
                                    if v_isSharedCheck_5036_ == 0 {
                                        v___x_5031_ = v___x_5028_;
                                        v_isShared_5032_ = v_isSharedCheck_5036_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5029_);
                                        lean_dec(v___x_5028_);
                                        v___x_5031_ = lean_box(0);
                                        v_isShared_5032_ = v_isSharedCheck_5036_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_5021_);
                            v_a_5012_ = v___x_5023_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5037_ = lean_ctor_get(v___x_5019_, 0);
                        v_isSharedCheck_5044_ = (!lean_is_exclusive(v___x_5019_)) as u8;
                        if v_isSharedCheck_5044_ == 0 {
                            v___x_5039_ = v___x_5019_;
                            v_isShared_5040_ = v_isSharedCheck_5044_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5037_);
                            lean_dec(v___x_5019_);
                            v___x_5039_ = lean_box(0);
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
                    v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
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
                    v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
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
    mut v_as_5045_: *mut LeanObject,
    mut v_sz_5046_: *mut LeanObject,
    mut v_i_5047_: *mut LeanObject,
    mut v_b_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
    mut v___y_5052_: *mut LeanObject,
    mut v___y_5053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5054_: usize = 0;
    let mut v_i_boxed_5055_: usize = 0;
    let mut v_res_5056_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5054_ = lean_unbox_usize(v_sz_5046_);
    lean_dec(v_sz_5046_);
    v_i_boxed_5055_ = lean_unbox_usize(v_i_5047_);
    lean_dec(v_i_5047_);
    v_res_5056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_as_5045_, v_sz_boxed_5054_, v_i_boxed_5055_, v_b_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
    lean_dec(v___y_5052_);
    lean_dec_ref(v___y_5051_);
    lean_dec(v___y_5050_);
    lean_dec_ref(v___y_5049_);
    lean_dec_ref(v_as_5045_);
    return v_res_5056_;
}
pub unsafe fn l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(
    mut v_decls_5057_: *mut LeanObject,
    mut v___y_5058_: *mut LeanObject,
    mut v___y_5059_: *mut LeanObject,
    mut v___y_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_5066_: u8 = 0;
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5069_: usize = 0;
    let mut v___x_5070_: usize = 0;
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5074_: u8 = 0;
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5078_: u8 = 0;
    let mut v_unused_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5063_ = lean_st_ref_get(v___y_5061_);
                v_env_5064_ = lean_ctor_get(v___x_5063_, 0);
                lean_inc_ref(v_env_5064_);
                lean_dec(v___x_5063_);
                v___x_5065_ = l_Lean_Environment_header(v_env_5064_);
                lean_dec_ref(v_env_5064_);
                v_isModule_5066_ = lean_ctor_get_uint8(
                    v___x_5065_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 4) as u32,
                );
                lean_dec_ref(v___x_5065_);
                if v_isModule_5066_ == 0 {
                    v___x_5067_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5067_, 0, v_decls_5057_);
                    return v___x_5067_;
                } else {
                    v___x_5068_ = lean_box(0);
                    v_sz_5069_ = lean_array_size(v_decls_5057_);
                    v___x_5070_ = 0usize;
                    v___x_5071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_checkTemplateVisibility_spec__0(v_decls_5057_, v_sz_5069_, v___x_5070_, v___x_5068_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
                    if lean_obj_tag(v___x_5071_) == 0 {
                        v_isSharedCheck_5078_ = (!lean_is_exclusive(v___x_5071_)) as u8;
                        if v_isSharedCheck_5078_ == 0 {
                            v_unused_5079_ = lean_ctor_get(v___x_5071_, 0);
                            lean_dec(v_unused_5079_);
                            v___x_5073_ = v___x_5071_;
                            v_isShared_5074_ = v_isSharedCheck_5078_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_5071_);
                            v___x_5073_ = lean_box(0);
                            v_isShared_5074_ = v_isSharedCheck_5078_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_decls_5057_);
                        v_a_5080_ = lean_ctor_get(v___x_5071_, 0);
                        v_isSharedCheck_5087_ = (!lean_is_exclusive(v___x_5071_)) as u8;
                        if v_isSharedCheck_5087_ == 0 {
                            v___x_5082_ = v___x_5071_;
                            v_isShared_5083_ = v_isSharedCheck_5087_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5080_);
                            lean_dec(v___x_5071_);
                            v___x_5082_ = lean_box(0);
                            v_isShared_5083_ = v_isSharedCheck_5087_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5074_ == 0 {
                    lean_ctor_set(v___x_5073_, 0, v_decls_5057_);
                    v___x_5076_ = v___x_5073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_decls_5057_);
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
                    v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
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
    mut v_decls_5088_: *mut LeanObject,
    mut v___y_5089_: *mut LeanObject,
    mut v___y_5090_: *mut LeanObject,
    mut v___y_5091_: *mut LeanObject,
    mut v___y_5092_: *mut LeanObject,
    mut v___y_5093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5094_: *mut LeanObject = core::ptr::null_mut();
    v_res_5094_ = l_Lean_Compiler_LCNF_checkTemplateVisibility___lam__0(
        v_decls_5088_,
        v___y_5089_,
        v___y_5090_,
        v___y_5091_,
        v___y_5092_,
    );
    lean_dec(v___y_5092_);
    lean_dec_ref(v___y_5091_);
    lean_dec(v___y_5090_);
    lean_dec_ref(v___y_5089_);
    return v_res_5094_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    v___x_5107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__0;
    v___x_5108_ = l_Lean_stringToMessageData(v___x_5107_);
    return v___x_5108_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(
    mut v_phase_5109_: u8,
    mut v___x_5110_: u8,
    mut v_as_5111_: *mut LeanObject,
    mut v_sz_5112_: usize,
    mut v_i_5113_: usize,
    mut v_b_5114_: *mut LeanObject,
    mut v___y_5115_: *mut LeanObject,
    mut v___y_5116_: *mut LeanObject,
    mut v___y_5117_: *mut LeanObject,
    mut v___y_5118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: usize = 0;
    let mut v___x_5123_: usize = 0;
    let mut v___x_5125_: u8 = 0;
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: u8 = 0;
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: u8 = 0;
    let mut v_options_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5143_: u8 = 0;
    let mut v_inheritedTraceOptions_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: u8 = 0;
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5125_ = lean_usize_dec_lt(v_i_5113_, v_sz_5112_);
                if v___x_5125_ == 0 {
                    v___x_5126_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5126_, 0, v_b_5114_);
                    return v___x_5126_;
                } else {
                    v___x_5127_ = lean_st_ref_get(v___y_5118_);
                    v_env_5128_ = lean_ctor_get(v___x_5127_, 0);
                    lean_inc_ref(v_env_5128_);
                    lean_dec(v___x_5127_);
                    v_a_5129_ = lean_array_uget_borrowed(v_as_5111_, v_i_5113_);
                    v_toSignature_5130_ = lean_ctor_get(v_a_5129_, 0);
                    v_name_5131_ = lean_ctor_get(v_toSignature_5130_, 0);
                    v___x_5132_ = lean_box(0);
                    v___x_5140_ = l_Lean_Environment_setExporting(v_env_5128_, v___x_5110_);
                    lean_inc(v_name_5131_);
                    v___x_5141_ =
                        l_Lean_Environment_contains(v___x_5140_, v_name_5131_, v___x_5110_);
                    if v___x_5141_ == 0 {
                        v_a_5121_ = v___x_5132_;
                        state = 1;
                        continue;
                    } else {
                        v_options_5142_ = lean_ctor_get(v___y_5117_, 2);
                        v_hasTrace_5143_ = lean_ctor_get_uint8(
                            v_options_5142_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_5143_ == 0 {
                            v___y_5134_ = v___y_5115_;
                            v___y_5135_ = v___y_5116_;
                            v___y_5136_ = v___y_5117_;
                            v___y_5137_ = v___y_5118_;
                            state = 2;
                            continue;
                        } else {
                            v_inheritedTraceOptions_5144_ = lean_ctor_get(v___y_5117_, 13);
                            v___x_5145_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2;
                            v___x_5146_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__5);
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
                                v___x_5148_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__7);
                                lean_inc(v_name_5131_);
                                v___x_5149_ = l_Lean_MessageData_ofName(v_name_5131_);
                                v___x_5150_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5150_, 0, v___x_5148_);
                                lean_ctor_set(v___x_5150_, 1, v___x_5149_);
                                v___x_5151_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0___closed__1);
                                v___x_5152_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5152_, 0, v___x_5150_);
                                lean_ctor_set(v___x_5152_, 1, v___x_5151_);
                                v___x_5153_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__0(v___x_5145_, v___x_5152_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_);
                                if lean_obj_tag(v___x_5153_) == 0 {
                                    lean_dec_ref_known(v___x_5153_, 1);
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
                lean_inc(v_a_5129_);
                v___x_5139_ = l_Lean_Compiler_LCNF_markDeclPublicRec(
                    v___x_5138_,
                    v_phase_5109_,
                    v_a_5129_,
                    v___y_5134_,
                    v___y_5135_,
                    v___y_5136_,
                    v___y_5137_,
                );
                if lean_obj_tag(v___x_5139_) == 0 {
                    lean_dec_ref_known(v___x_5139_, 1);
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
    mut v_phase_5154_: *mut LeanObject,
    mut v___x_5155_: *mut LeanObject,
    mut v_as_5156_: *mut LeanObject,
    mut v_sz_5157_: *mut LeanObject,
    mut v_i_5158_: *mut LeanObject,
    mut v_b_5159_: *mut LeanObject,
    mut v___y_5160_: *mut LeanObject,
    mut v___y_5161_: *mut LeanObject,
    mut v___y_5162_: *mut LeanObject,
    mut v___y_5163_: *mut LeanObject,
    mut v___y_5164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_boxed_5165_: u8 = 0;
    let mut v___x_2836__boxed_5166_: u8 = 0;
    let mut v_sz_boxed_5167_: usize = 0;
    let mut v_i_boxed_5168_: usize = 0;
    let mut v_res_5169_: *mut LeanObject = core::ptr::null_mut();
    v_phase_boxed_5165_ = (lean_unbox(v_phase_5154_) as u8);
    v___x_2836__boxed_5166_ = (lean_unbox(v___x_5155_) as u8);
    v_sz_boxed_5167_ = lean_unbox_usize(v_sz_5157_);
    lean_dec(v_sz_5157_);
    v_i_boxed_5168_ = lean_unbox_usize(v_i_5158_);
    lean_dec(v_i_5158_);
    v_res_5169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_boxed_5165_, v___x_2836__boxed_5166_, v_as_5156_, v_sz_boxed_5167_, v_i_boxed_5168_, v_b_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_);
    lean_dec(v___y_5163_);
    lean_dec_ref(v___y_5162_);
    lean_dec(v___y_5161_);
    lean_dec_ref(v___y_5160_);
    lean_dec_ref(v_as_5156_);
    return v_res_5169_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inferVisibility___lam__0(
    mut v_phase_5170_: u8,
    mut v_decls_5171_: *mut LeanObject,
    mut v___y_5172_: *mut LeanObject,
    mut v___y_5173_: *mut LeanObject,
    mut v___y_5174_: *mut LeanObject,
    mut v___y_5175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_5180_: u8 = 0;
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5183_: usize = 0;
    let mut v___x_5184_: usize = 0;
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5188_: u8 = 0;
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5192_: u8 = 0;
    let mut v_unused_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5197_: u8 = 0;
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5177_ = lean_st_ref_get(v___y_5175_);
                v_env_5178_ = lean_ctor_get(v___x_5177_, 0);
                lean_inc_ref(v_env_5178_);
                lean_dec(v___x_5177_);
                v___x_5179_ = l_Lean_Environment_header(v_env_5178_);
                lean_dec_ref(v_env_5178_);
                v_isModule_5180_ = lean_ctor_get_uint8(
                    v___x_5179_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 4) as u32,
                );
                lean_dec_ref(v___x_5179_);
                if v_isModule_5180_ == 0 {
                    v___x_5181_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5181_, 0, v_decls_5171_);
                    return v___x_5181_;
                } else {
                    v___x_5182_ = lean_box(0);
                    v_sz_5183_ = lean_array_size(v_decls_5171_);
                    v___x_5184_ = 0usize;
                    v___x_5185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_inferVisibility_spec__0(v_phase_5170_, v_isModule_5180_, v_decls_5171_, v_sz_5183_, v___x_5184_, v___x_5182_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
                    if lean_obj_tag(v___x_5185_) == 0 {
                        v_isSharedCheck_5192_ = (!lean_is_exclusive(v___x_5185_)) as u8;
                        if v_isSharedCheck_5192_ == 0 {
                            v_unused_5193_ = lean_ctor_get(v___x_5185_, 0);
                            lean_dec(v_unused_5193_);
                            v___x_5187_ = v___x_5185_;
                            v_isShared_5188_ = v_isSharedCheck_5192_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_5185_);
                            v___x_5187_ = lean_box(0);
                            v_isShared_5188_ = v_isSharedCheck_5192_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_decls_5171_);
                        v_a_5194_ = lean_ctor_get(v___x_5185_, 0);
                        v_isSharedCheck_5201_ = (!lean_is_exclusive(v___x_5185_)) as u8;
                        if v_isSharedCheck_5201_ == 0 {
                            v___x_5196_ = v___x_5185_;
                            v_isShared_5197_ = v_isSharedCheck_5201_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5194_);
                            lean_dec(v___x_5185_);
                            v___x_5196_ = lean_box(0);
                            v_isShared_5197_ = v_isSharedCheck_5201_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5188_ == 0 {
                    lean_ctor_set(v___x_5187_, 0, v_decls_5171_);
                    v___x_5190_ = v___x_5187_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_decls_5171_);
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
                    v_reuseFailAlloc_5200_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
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
    mut v_phase_5202_: *mut LeanObject,
    mut v_decls_5203_: *mut LeanObject,
    mut v___y_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_boxed_5209_: u8 = 0;
    let mut v_res_5210_: *mut LeanObject = core::ptr::null_mut();
    v_phase_boxed_5209_ = (lean_unbox(v_phase_5202_) as u8);
    v_res_5210_ = l_Lean_Compiler_LCNF_inferVisibility___lam__0(
        v_phase_boxed_5209_,
        v_decls_5203_,
        v___y_5204_,
        v___y_5205_,
        v___y_5206_,
        v___y_5207_,
    );
    lean_dec(v___y_5207_);
    lean_dec_ref(v___y_5206_);
    lean_dec(v___y_5205_);
    lean_dec_ref(v___y_5204_);
    return v_res_5210_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inferVisibility(mut v_phase_5213_: u8) -> *mut LeanObject {
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: u8 = 0;
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    v___x_5214_ = lean_box((v_phase_5213_) as usize);
    v___f_5215_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_inferVisibility___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_5215_, 0, v___x_5214_);
    v___x_5216_ = lean_unsigned_to_nat(0);
    v___x_5217_ = 0;
    v___x_5218_ = l_Lean_Compiler_LCNF_inferVisibility___closed__0;
    v___x_5219_ = lean_alloc_ctor(0, 3, (3) as u32);
    lean_ctor_set(v___x_5219_, 0, v___x_5216_);
    lean_ctor_set(v___x_5219_, 1, v___x_5218_);
    lean_ctor_set(v___x_5219_, 2, v___f_5215_);
    lean_ctor_set_uint8(
        v___x_5219_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_phase_5213_,
    );
    lean_ctor_set_uint8(
        v___x_5219_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
        v_phase_5213_,
    );
    lean_ctor_set_uint8(
        v___x_5219_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
        v___x_5217_,
    );
    return v___x_5219_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inferVisibility___boxed(
    mut v_phase_5220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_boxed_5221_: u8 = 0;
    let mut v_res_5222_: *mut LeanObject = core::ptr::null_mut();
    v_phase_boxed_5221_ = (lean_unbox(v_phase_5220_) as u8);
    v_res_5222_ = l_Lean_Compiler_LCNF_inferVisibility(v_phase_boxed_5221_);
    return v_res_5222_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    v___x_5274_ = lean_unsigned_to_nat(3356661454);
    v___x_5275_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_;
    v___x_5276_ = l_Lean_Name_num___override(v___x_5275_, v___x_5274_);
    return v___x_5276_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    v___x_5278_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_;
    v___x_5279_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
    v___x_5280_ = l_Lean_Name_str___override(v___x_5279_, v___x_5278_);
    return v___x_5280_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    v___x_5282_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_;
    v___x_5283_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
    v___x_5284_ = l_Lean_Name_str___override(v___x_5283_, v___x_5282_);
    return v___x_5284_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    v___x_5285_ = lean_unsigned_to_nat(2);
    v___x_5286_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
    v___x_5287_ = l_Lean_Name_num___override(v___x_5286_, v___x_5285_);
    return v___x_5287_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: u8 = 0;
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    v___x_5289_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_markDeclPublicRec_spec__1___closed__2;
    v___x_5290_ = 0;
    v___x_5291_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_);
    v___x_5292_ = l_Lean_registerTraceClass(v___x_5289_, v___x_5290_, v___x_5291_);
    return v___x_5292_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2____boxed(
    mut v_a_5293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5294_: *mut LeanObject = core::ptr::null_mut();
    v_res_5294_ = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
    return v_res_5294_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Visibility(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_Visibility_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Visibility_3356661454____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Visibility(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Visibility(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Visibility(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Visibility(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Visibility(builtin);
}

// Lean compiler output
// Module: Lean.Compiler.CSimpAttr
// Imports: Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.ExtraModUses
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_level_eq, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land,
    lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_replaceRef, l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_ensureNoArgs, l_Lean_ensureAttrDeclIsPublic,
    l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg, l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_constLevels_x21,
    l_Lean_Expr_isAppOfArity, l_Lean_mkConst,
};
use crate::r#gen::Lean::ExtraModUses::{
    initialize_Lean_ExtraModUses, l___private_Lean_ExtraModUses_0__Lean_extraModUses,
    l_Lean_indirectModUseExt, l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
    runtime_initialize_Lean_ExtraModUses,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_hash, l_Lean_Level_isParam};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    initialize_Lean_ScopedEnvExtension, l_Lean_ScopedEnvExtension_addCore___redArg,
    l_Lean_ScopedEnvExtension_getState___redArg, l_Lean_registerSimpleScopedEnvExtension___redArg,
    runtime_initialize_Lean_ScopedEnvExtension,
};
use crate::r#gen::Lean::Util::Recognizers::{
    initialize_Lean_Util_Recognizers, runtime_initialize_Lean_Util_Recognizers,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
pub static l_Lean_Compiler_CSimp_instInhabitedEntry_default___closed__0_value:
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
static mut l_Lean_Compiler_CSimp_instInhabitedEntry_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_CSimp_instInhabitedEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_CSimp_instInhabitedEntry_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_CSimp_instInhabitedEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_CSimp_instInhabitedEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_CSimp_instInhabitedEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_CSimp_instInhabitedState_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_CSimp_instInhabitedState: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_CSimp_State_switch as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [67, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 120, 116, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2506120210329473605 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16700278000057647119 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_CSimp_ext: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_CSimp_add___closed__0_value: leanh::LeanStringObject<103> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 103,
        m_capacity: 103,
        m_length: 102,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 115, 105, 109, 112, 39, 32, 116, 104,
            101, 111, 114, 101, 109, 44, 32, 111, 110, 108, 121, 32, 99, 111, 110, 115, 116, 97,
            110, 116, 32, 114, 101, 112, 108, 97, 99, 101, 109, 101, 110, 116, 32, 116, 104, 101,
            111, 114, 101, 109, 115, 32, 40, 101, 46, 103, 46, 44, 32, 96, 64, 102, 32, 61, 32, 64,
            103, 96, 41, 32, 97, 114, 101, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32, 115,
            117, 112, 112, 111, 114, 116, 101, 100, 46, 0,
        ],
    };
static mut l_Lean_Compiler_CSimp_add___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_CSimp_add___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_CSimp_add___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_CSimp_add___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__2_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_value:
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
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_value
        ) as *mut leanh::LeanObject,
        11079354408986465895 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1501781890156459336 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [67, 83, 105, 109, 112, 65, 116, 116, 114, 0],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_value:
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
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_value
        ) as *mut leanh::LeanObject,
        2541629466078937915 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        11902246563960517958 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12348749176669000783 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8798584843508670593 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6759957689071080516 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__10_value:
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
    m_data: [105, 110, 105, 116, 70, 110, 0],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__10_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__11_value:
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
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__9_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__10_value
        ) as *mut leanh::LeanObject,
        14890345188404749281 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__11_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__12_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 115, 105, 109, 112, 0],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__12_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13_value:
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
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__12_value
        ) as *mut leanh::LeanObject,
        6868535136644065322 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__14_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__14_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__15_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__15_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__16_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111,
        114, 101, 109, 32, 102, 111, 114, 32, 116, 104, 101, 32, 99, 111, 109, 112, 105, 108, 101,
        114, 0,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__16_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__17_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__11_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__16_value
        ) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__17:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__17_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__18_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__17_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__14_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__15_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__18_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1___closed__0_value: leanh::LeanStringObject<863> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 863, m_capacity: 863, m_length: 862, m_data: [84, 97, 103, 115, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 115, 44, 32, 119, 104, 105, 99, 104, 32, 97, 108, 108, 111, 119, 32, 111, 110, 101, 32, 118, 97, 108, 117, 101, 32, 116, 111, 32, 98, 101, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 98, 121, 32, 97, 110, 111, 116, 104, 101, 114, 32, 101, 113, 117, 97, 108, 32, 118, 97, 108, 117, 101, 10, 105, 110, 32, 99, 111, 109, 112, 105, 108, 101, 100, 32, 99, 111, 100, 101, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 116, 121, 112, 105, 99, 97, 108, 108, 121, 32, 117, 115, 101, 100, 32, 116, 111, 32, 114, 101, 112, 108, 97, 99, 101, 32, 97, 32, 115, 108, 111, 119, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 119, 104, 111, 115, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 105, 115, 32, 99, 111, 110, 118, 101, 110, 105, 101, 110, 116, 10, 105, 110, 32, 112, 114, 111, 111, 102, 115, 32, 119, 105, 116, 104, 32, 97, 32, 102, 97, 115, 116, 101, 114, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 32, 111, 114, 32, 116, 111, 32, 109, 97, 107, 101, 32, 110, 111, 110, 99, 111, 109, 112, 117, 116, 97, 98, 108, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 99, 111, 109, 112, 117, 116, 97, 98, 108, 101, 46, 32, 73, 110, 32, 112, 97, 114, 116, 105, 99, 117, 108, 97, 114, 44, 10, 109, 97, 110, 121, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 115, 32, 111, 110, 32, 108, 105, 115, 116, 115, 32, 97, 110, 100, 32, 97, 114, 114, 97, 121, 115, 32, 97, 114, 101, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 98, 121, 32, 116, 97, 105, 108, 45, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 115, 46, 10, 10, 65, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 32, 99, 97, 110, 110, 111, 116, 32, 116, 97, 107, 101, 32, 97, 110, 121, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 110, 100, 32, 109, 117, 115, 116, 32, 112, 114, 111, 118, 101, 32, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 96, 64, 102, 32, 61, 32, 64, 103, 96, 10, 119, 104, 101, 114, 101, 32, 96, 102, 96, 32, 97, 110, 100, 32, 96, 103, 96, 32, 109, 97, 121, 32, 98, 101, 32, 97, 114, 98, 105, 116, 114, 97, 114, 121, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 46, 32, 73, 110, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 97, 102, 116, 101, 114, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 116, 97, 103, 103, 101, 100, 10, 96, 64, 91, 99, 115, 105, 109, 112, 93, 96, 44, 32, 97, 110, 121, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32, 111, 102, 32, 96, 102, 96, 32, 105, 115, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 119, 105, 116, 104, 32, 96, 103, 96, 32, 105, 110, 32, 99, 111, 109, 112, 105, 108, 101, 100, 32, 99, 111, 100, 101, 44, 32, 98, 117, 116, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 116, 121, 112, 101, 10, 116, 104, 101, 111, 114, 121, 46, 32, 73, 110, 32, 116, 104, 105, 115, 32, 115, 101, 110, 115, 101, 44, 32, 96, 64, 91, 99, 115, 105, 109, 112, 93, 96, 32, 105, 115, 32, 97, 32, 115, 97, 102, 101, 114, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 116, 111, 32, 96, 64, 91, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 95, 98, 121, 93, 96, 46, 10, 10, 72, 111, 119, 101, 118, 101, 114, 32, 105, 116, 32, 105, 115, 32, 115, 116, 105, 108, 108, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32, 117, 110, 115, 111, 117, 110, 100, 32, 96, 64, 91, 99, 115, 105, 109, 112, 93, 96, 32, 108, 101, 109, 109, 97, 115, 32, 98, 121, 32, 117, 115, 105, 110, 103, 32, 96, 117, 110, 115, 97, 102, 101, 96, 32, 111, 114, 32, 117, 110, 115, 111, 117, 110, 100, 10, 97, 120, 105, 111, 109, 115, 32, 40, 108, 105, 107, 101, 32, 96, 115, 111, 114, 114, 121, 65, 120, 96, 41, 46, 10, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__3_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__3_value) as *mut leanh::LeanObject,7870113334857981723 as *mut leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__5_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__10_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__10_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__11_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__13_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__15_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__15_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__17_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__18_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__19_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__20_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__3_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__3_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2264_ = leanh::lean_box(0);
    v___x_2265_ = leanh::lean_unsigned_to_nat(16);
    v___x_2266_ = lean_mk_array(v___x_2265_, v___x_2264_);
    return v___x_2266_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0,
    );
    v___x_2268_ = leanh::lean_unsigned_to_nat(0);
    v___x_2269_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2269_, 0, v___x_2268_);
    leanh::lean_ctor_set(v___x_2269_, 1, v___x_2267_);
    return v___x_2269_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2270_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2270_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2271_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2,
    );
    v___x_2272_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2272_, 0, v___x_2271_);
    return v___x_2272_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: u8 = 0;
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3,
    );
    v___x_2274_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1,
    );
    v___x_2275_ = 1;
    v___x_2276_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_2276_, 0, v___x_2274_);
    leanh::lean_ctor_set(v___x_2276_, 1, v___x_2273_);
    leanh::lean_ctor_set_uint8(
        v___x_2276_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_2275_,
    );
    return v___x_2276_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2277_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4,
    );
    v___x_2278_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2278_, 0, v___x_2277_);
    leanh::lean_ctor_set(v___x_2278_, 1, v___x_2277_);
    return v___x_2278_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default()
-> *mut leanh::LeanObject {
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2279_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5,
    );
    return v___x_2279_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState() -> *mut leanh::LeanObject {
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ = l_Lean_Compiler_CSimp_instInhabitedState_default;
    return v___x_2280_;
}
pub unsafe fn l_Lean_SMap_switch___at___00Lean_Compiler_CSimp_State_switch_spec__0___redArg(
    mut v_m_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_2282_: u8 = 0;
    let mut v_map_u2081_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2287_: u8 = 0;
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_2282_ = leanh::lean_ctor_get_uint8(
                    v_m_2281_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_2282_ == 0 {
                    return v_m_2281_;
                } else {
                    v_map_u2081_2283_ = leanh::lean_ctor_get(v_m_2281_, 0);
                    v_map_u2082_2284_ = leanh::lean_ctor_get(v_m_2281_, 1);
                    v_isSharedCheck_2292_ = (!leanh::lean_is_exclusive(v_m_2281_)) as u8;
                    if v_isSharedCheck_2292_ == 0 {
                        v___x_2286_ = v_m_2281_;
                        v_isShared_2287_ = v_isSharedCheck_2292_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_2284_);
                        leanh::lean_inc(v_map_u2081_2283_);
                        leanh::lean_dec(v_m_2281_);
                        v___x_2286_ = leanh::lean_box(0);
                        v_isShared_2287_ = v_isSharedCheck_2292_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2288_ = 0;
                if v_isShared_2287_ == 0 {
                    v___x_2290_ = v___x_2286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2291_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_map_u2081_2283_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_map_u2082_2284_);
                    v___x_2290_ = v_reuseFailAlloc_2291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2290_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_2288_,
                );
                return v___x_2290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00Lean_Compiler_CSimp_State_switch_spec__0(
    mut v_00_u03b2_2293_: *mut leanh::LeanObject,
    mut v_m_2294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2295_ =
        l_Lean_SMap_switch___at___00Lean_Compiler_CSimp_State_switch_spec__0___redArg(v_m_2294_);
    return v___x_2295_;
}
pub unsafe fn l_Lean_Compiler_CSimp_State_switch(
    mut v_x_2296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_thmNames_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2297_ = leanh::lean_ctor_get(v_x_2296_, 0);
                v_thmNames_2298_ = leanh::lean_ctor_get(v_x_2296_, 1);
                v_isSharedCheck_2307_ = (!leanh::lean_is_exclusive(v_x_2296_)) as u8;
                if v_isSharedCheck_2307_ == 0 {
                    v___x_2300_ = v_x_2296_;
                    v_isShared_2301_ = v_isSharedCheck_2307_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_thmNames_2298_);
                    leanh::lean_inc(v_map_2297_);
                    leanh::lean_dec(v_x_2296_);
                    v___x_2300_ = leanh::lean_box(0);
                    v_isShared_2301_ = v_isSharedCheck_2307_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2302_ =
                    l_Lean_SMap_switch___at___00Lean_Compiler_CSimp_State_switch_spec__0___redArg(
                        v_map_2297_,
                    );
                v___x_2303_ =
                    l_Lean_SMap_switch___at___00Lean_Compiler_CSimp_State_switch_spec__0___redArg(
                        v_thmNames_2298_,
                    );
                if v_isShared_2301_ == 0 {
                    leanh::lean_ctor_set(v___x_2300_, 1, v___x_2303_);
                    leanh::lean_ctor_set(v___x_2300_, 0, v___x_2302_);
                    v___x_2305_ = v___x_2300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2306_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 1, v___x_2303_);
                    v___x_2305_ = v_reuseFailAlloc_2306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_(
    mut v_x_2308_: *mut leanh::LeanObject,
    mut v_a_2309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2310_, 0, v_a_2309_);
    leanh::lean_inc_ref_n(v___x_2310_, 2);
    v___x_2311_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2311_, 0, v___x_2310_);
    leanh::lean_ctor_set(v___x_2311_, 1, v___x_2310_);
    leanh::lean_ctor_set(v___x_2311_, 2, v___x_2310_);
    return v___x_2311_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2____boxed(
    mut v_x_2312_: *mut leanh::LeanObject,
    mut v_a_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2314_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_(v_x_2312_, v_a_2313_);
    leanh::lean_dec_ref(v_x_2312_);
    return v_res_2314_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_2315_: *mut leanh::LeanObject,
    mut v_x_2316_: *mut leanh::LeanObject,
    mut v_x_2317_: *mut leanh::LeanObject,
    mut v_x_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2319_ = leanh::lean_ctor_get(v_x_2315_, 0);
                v_vs_2320_ = leanh::lean_ctor_get(v_x_2315_, 1);
                v_isSharedCheck_2344_ = (!leanh::lean_is_exclusive(v_x_2315_)) as u8;
                if v_isSharedCheck_2344_ == 0 {
                    v___x_2322_ = v_x_2315_;
                    v_isShared_2323_ = v_isSharedCheck_2344_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2320_);
                    leanh::lean_inc(v_ks_2319_);
                    leanh::lean_dec(v_x_2315_);
                    v___x_2322_ = leanh::lean_box(0);
                    v_isShared_2323_ = v_isSharedCheck_2344_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2324_ = lean_array_get_size(v_ks_2319_);
                v___x_2325_ = lean_nat_dec_lt(v_x_2316_, v___x_2324_);
                if v___x_2325_ == 0 {
                    leanh::lean_dec(v_x_2316_);
                    v___x_2326_ = lean_array_push(v_ks_2319_, v_x_2317_);
                    v___x_2327_ = lean_array_push(v_vs_2320_, v_x_2318_);
                    if v_isShared_2323_ == 0 {
                        leanh::lean_ctor_set(v___x_2322_, 1, v___x_2327_);
                        leanh::lean_ctor_set(v___x_2322_, 0, v___x_2326_);
                        v___x_2329_ = v___x_2322_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2330_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2326_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2327_);
                        v___x_2329_ = v_reuseFailAlloc_2330_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2331_ = lean_array_fget_borrowed(v_ks_2319_, v_x_2316_);
                    v___x_2332_ = lean_name_eq(v_x_2317_, v_k_x27_2331_);
                    if v___x_2332_ == 0 {
                        if v_isShared_2323_ == 0 {
                            v___x_2334_ = v___x_2322_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2338_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_ks_2319_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_vs_2320_);
                            v___x_2334_ = v_reuseFailAlloc_2338_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2339_ = lean_array_fset(v_ks_2319_, v_x_2316_, v_x_2317_);
                        v___x_2340_ = lean_array_fset(v_vs_2320_, v_x_2316_, v_x_2318_);
                        leanh::lean_dec(v_x_2316_);
                        if v_isShared_2323_ == 0 {
                            leanh::lean_ctor_set(v___x_2322_, 1, v___x_2340_);
                            leanh::lean_ctor_set(v___x_2322_, 0, v___x_2339_);
                            v___x_2342_ = v___x_2322_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2343_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2339_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2340_);
                            v___x_2342_ = v_reuseFailAlloc_2343_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2329_;
            }
            3 => {
                v___x_2335_ = leanh::lean_unsigned_to_nat(1);
                v___x_2336_ = lean_nat_add(v_x_2316_, v___x_2335_);
                leanh::lean_dec(v_x_2316_);
                v_x_2315_ = v___x_2334_;
                v_x_2316_ = v___x_2336_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_2345_: *mut leanh::LeanObject,
    mut v_k_2346_: *mut leanh::LeanObject,
    mut v_v_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = leanh::lean_unsigned_to_nat(0);
    v___x_2349_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_n_2345_, v___x_2348_, v_k_2346_, v_v_2347_);
    return v___x_2349_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: u64 = 0;
    v___x_2350_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2351_ = lean_uint64_of_nat(v___x_2350_);
    return v___x_2351_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_2352_: usize = 0;
    let mut v___x_2353_: usize = 0;
    let mut v___x_2354_: usize = 0;
    v___x_2352_ = 5usize;
    v___x_2353_ = 1usize;
    v___x_2354_ = lean_usize_shift_left(v___x_2353_, v___x_2352_);
    return v___x_2354_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_2355_: usize = 0;
    let mut v___x_2356_: usize = 0;
    let mut v___x_2357_: usize = 0;
    v___x_2355_ = 1usize;
    v___x_2356_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_2357_ = lean_usize_sub(v___x_2356_, v___x_2355_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2358_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_x_2359_: *mut leanh::LeanObject,
    mut v_x_2360_: usize,
    mut v_x_2361_: usize,
    mut v_x_2362_: *mut leanh::LeanObject,
    mut v_x_2363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: usize = 0;
    let mut v___x_2366_: usize = 0;
    let mut v___x_2367_: usize = 0;
    let mut v___x_2368_: usize = 0;
    let mut v_j_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u8 = 0;
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2374_: u8 = 0;
    let mut v_v_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v___x_2389_: u8 = 0;
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_node_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v___x_2400_: usize = 0;
    let mut v___x_2401_: usize = 0;
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2408_: u8 = 0;
    let mut v_unused_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2419_: u8 = 0;
    let mut v_ks_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: usize = 0;
    let mut v___x_2426_: u8 = 0;
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: u8 = 0;
    let mut v_reuseFailAlloc_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2359_) == 0 {
                    v_es_2364_ = leanh::lean_ctor_get(v_x_2359_, 0);
                    v___x_2365_ = 5usize;
                    v___x_2366_ = 1usize;
                    v___x_2367_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_2368_ = lean_usize_land(v_x_2360_, v___x_2367_);
                    v_j_2369_ = lean_usize_to_nat(v___x_2368_);
                    v___x_2370_ = lean_array_get_size(v_es_2364_);
                    v___x_2371_ = lean_nat_dec_lt(v_j_2369_, v___x_2370_);
                    if v___x_2371_ == 0 {
                        leanh::lean_dec(v_j_2369_);
                        leanh::lean_dec(v_x_2363_);
                        leanh::lean_dec(v_x_2362_);
                        return v_x_2359_;
                    } else {
                        leanh::lean_inc_ref(v_es_2364_);
                        v_isSharedCheck_2408_ = (!leanh::lean_is_exclusive(v_x_2359_)) as u8;
                        if v_isSharedCheck_2408_ == 0 {
                            v_unused_2409_ = leanh::lean_ctor_get(v_x_2359_, 0);
                            leanh::lean_dec(v_unused_2409_);
                            v___x_2373_ = v_x_2359_;
                            v_isShared_2374_ = v_isSharedCheck_2408_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2359_);
                            v___x_2373_ = leanh::lean_box(0);
                            v_isShared_2374_ = v_isSharedCheck_2408_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2410_ = leanh::lean_ctor_get(v_x_2359_, 0);
                    v_vs_2411_ = leanh::lean_ctor_get(v_x_2359_, 1);
                    v_isSharedCheck_2431_ = (!leanh::lean_is_exclusive(v_x_2359_)) as u8;
                    if v_isSharedCheck_2431_ == 0 {
                        v___x_2413_ = v_x_2359_;
                        v_isShared_2414_ = v_isSharedCheck_2431_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2411_);
                        leanh::lean_inc(v_ks_2410_);
                        leanh::lean_dec(v_x_2359_);
                        v___x_2413_ = leanh::lean_box(0);
                        v_isShared_2414_ = v_isSharedCheck_2431_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2375_ = lean_array_fget(v_es_2364_, v_j_2369_);
                v___x_2376_ = leanh::lean_box(0);
                v_xs_x27_2377_ = lean_array_fset(v_es_2364_, v_j_2369_, v___x_2376_);
                match leanh::lean_obj_tag(v_v_2375_) {
                    0 => {
                        v_key_2384_ = leanh::lean_ctor_get(v_v_2375_, 0);
                        v_val_2385_ = leanh::lean_ctor_get(v_v_2375_, 1);
                        v_isSharedCheck_2395_ = (!leanh::lean_is_exclusive(v_v_2375_)) as u8;
                        if v_isSharedCheck_2395_ == 0 {
                            v___x_2387_ = v_v_2375_;
                            v_isShared_2388_ = v_isSharedCheck_2395_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2385_);
                            leanh::lean_inc(v_key_2384_);
                            leanh::lean_dec(v_v_2375_);
                            v___x_2387_ = leanh::lean_box(0);
                            v_isShared_2388_ = v_isSharedCheck_2395_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2396_ = leanh::lean_ctor_get(v_v_2375_, 0);
                        v_isSharedCheck_2406_ = (!leanh::lean_is_exclusive(v_v_2375_)) as u8;
                        if v_isSharedCheck_2406_ == 0 {
                            v___x_2398_ = v_v_2375_;
                            v_isShared_2399_ = v_isSharedCheck_2406_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2396_);
                            leanh::lean_dec(v_v_2375_);
                            v___x_2398_ = leanh::lean_box(0);
                            v_isShared_2399_ = v_isSharedCheck_2406_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2407_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2407_, 0, v_x_2362_);
                        leanh::lean_ctor_set(v___x_2407_, 1, v_x_2363_);
                        v___y_2379_ = v___x_2407_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2380_ = lean_array_fset(v_xs_x27_2377_, v_j_2369_, v___y_2379_);
                leanh::lean_dec(v_j_2369_);
                if v_isShared_2374_ == 0 {
                    leanh::lean_ctor_set(v___x_2373_, 0, v___x_2380_);
                    v___x_2382_ = v___x_2373_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2383_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
                    v___x_2382_ = v_reuseFailAlloc_2383_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2382_;
            }
            4 => {
                v___x_2389_ = lean_name_eq(v_x_2362_, v_key_2384_);
                if v___x_2389_ == 0 {
                    leanh::lean_del_object(v___x_2387_);
                    v___x_2390_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2384_,
                        v_val_2385_,
                        v_x_2362_,
                        v_x_2363_,
                    );
                    v___x_2391_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2391_, 0, v___x_2390_);
                    v___y_2379_ = v___x_2391_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2385_);
                    leanh::lean_dec(v_key_2384_);
                    if v_isShared_2388_ == 0 {
                        leanh::lean_ctor_set(v___x_2387_, 1, v_x_2363_);
                        leanh::lean_ctor_set(v___x_2387_, 0, v_x_2362_);
                        v___x_2393_ = v___x_2387_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2394_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_x_2362_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_x_2363_);
                        v___x_2393_ = v_reuseFailAlloc_2394_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2379_ = v___x_2393_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2400_ = lean_usize_shift_right(v_x_2360_, v___x_2365_);
                v___x_2401_ = lean_usize_add(v_x_2361_, v___x_2366_);
                v___x_2402_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_node_2396_, v___x_2400_, v___x_2401_, v_x_2362_, v_x_2363_);
                if v_isShared_2399_ == 0 {
                    leanh::lean_ctor_set(v___x_2398_, 0, v___x_2402_);
                    v___x_2404_ = v___x_2398_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2405_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
                    v___x_2404_ = v_reuseFailAlloc_2405_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2379_ = v___x_2404_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2414_ == 0 {
                    v___x_2416_ = v___x_2413_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2430_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_ks_2410_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_vs_2411_);
                    v___x_2416_ = v_reuseFailAlloc_2430_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2417_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v___x_2416_, v_x_2362_, v_x_2363_);
                v___x_2425_ = 7usize;
                v___x_2426_ = lean_usize_dec_le(v___x_2425_, v_x_2361_);
                if v___x_2426_ == 0 {
                    v___x_2427_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2417_);
                    v___x_2428_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2429_ = lean_nat_dec_lt(v___x_2427_, v___x_2428_);
                    leanh::lean_dec(v___x_2427_);
                    v___y_2419_ = v___x_2429_;
                    state = 10;
                    continue;
                } else {
                    v___y_2419_ = v___x_2426_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2419_ == 0 {
                    v_ks_2420_ = leanh::lean_ctor_get(v_newNode_2417_, 0);
                    leanh::lean_inc_ref(v_ks_2420_);
                    v_vs_2421_ = leanh::lean_ctor_get(v_newNode_2417_, 1);
                    leanh::lean_inc_ref(v_vs_2421_);
                    leanh::lean_dec_ref(v_newNode_2417_);
                    v___x_2422_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2423_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_2424_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_2361_, v_ks_2420_, v_vs_2421_, v___x_2422_, v___x_2423_);
                    leanh::lean_dec_ref(v_vs_2421_);
                    leanh::lean_dec_ref(v_ks_2420_);
                    return v___x_2424_;
                } else {
                    return v_newNode_2417_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_2432_: usize,
    mut v_keys_2433_: *mut leanh::LeanObject,
    mut v_vals_2434_: *mut leanh::LeanObject,
    mut v_i_2435_: *mut leanh::LeanObject,
    mut v_entries_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: u8 = 0;
    let mut v_k_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: u64 = 0;
    let mut v_h_2443_: usize = 0;
    let mut v___x_2444_: usize = 0;
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: usize = 0;
    let mut v___x_2447_: usize = 0;
    let mut v___x_2448_: usize = 0;
    let mut v_h_2449_: usize = 0;
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: u64 = 0;
    let mut v_hash_2454_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2437_ = lean_array_get_size(v_keys_2433_);
                v___x_2438_ = lean_nat_dec_lt(v_i_2435_, v___x_2437_);
                if v___x_2438_ == 0 {
                    leanh::lean_dec(v_i_2435_);
                    return v_entries_2436_;
                } else {
                    v_k_2439_ = lean_array_fget_borrowed(v_keys_2433_, v_i_2435_);
                    v_v_2440_ = lean_array_fget_borrowed(v_vals_2434_, v_i_2435_);
                    if leanh::lean_obj_tag(v_k_2439_) == 0 {
                        v___x_2453_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                        v___y_2442_ = v___x_2453_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2454_ = leanh::lean_ctor_get_uint64(
                            v_k_2439_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2442_ = v_hash_2454_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2443_ = lean_uint64_to_usize(v___y_2442_);
                v___x_2444_ = 5usize;
                v___x_2445_ = leanh::lean_unsigned_to_nat(1);
                v___x_2446_ = 1usize;
                v___x_2447_ = lean_usize_sub(v_depth_2432_, v___x_2446_);
                v___x_2448_ = lean_usize_mul(v___x_2444_, v___x_2447_);
                v_h_2449_ = lean_usize_shift_right(v_h_2443_, v___x_2448_);
                v___x_2450_ = lean_nat_add(v_i_2435_, v___x_2445_);
                leanh::lean_dec(v_i_2435_);
                leanh::lean_inc(v_v_2440_);
                leanh::lean_inc(v_k_2439_);
                v___x_2451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_entries_2436_, v_h_2449_, v_depth_2432_, v_k_2439_, v_v_2440_);
                v_i_2435_ = v___x_2450_;
                v_entries_2436_ = v___x_2451_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_2455_: *mut leanh::LeanObject,
    mut v_keys_2456_: *mut leanh::LeanObject,
    mut v_vals_2457_: *mut leanh::LeanObject,
    mut v_i_2458_: *mut leanh::LeanObject,
    mut v_entries_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2460_: usize = 0;
    let mut v_res_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2460_ = leanh::lean_unbox_usize(v_depth_2455_);
    leanh::lean_dec(v_depth_2455_);
    v_res_2461_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_2460_, v_keys_2456_, v_vals_2457_, v_i_2458_, v_entries_2459_);
    leanh::lean_dec_ref(v_vals_2457_);
    leanh::lean_dec_ref(v_keys_2456_);
    return v_res_2461_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2462_: *mut leanh::LeanObject,
    mut v_x_2463_: *mut leanh::LeanObject,
    mut v_x_2464_: *mut leanh::LeanObject,
    mut v_x_2465_: *mut leanh::LeanObject,
    mut v_x_2466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_887__boxed_2467_: usize = 0;
    let mut v_x_888__boxed_2468_: usize = 0;
    let mut v_res_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_887__boxed_2467_ = leanh::lean_unbox_usize(v_x_2463_);
    leanh::lean_dec(v_x_2463_);
    v_x_888__boxed_2468_ = leanh::lean_unbox_usize(v_x_2464_);
    leanh::lean_dec(v_x_2464_);
    v_res_2469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2462_, v_x_887__boxed_2467_, v_x_888__boxed_2468_, v_x_2465_, v_x_2466_);
    return v_res_2469_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_2470_: *mut leanh::LeanObject,
    mut v_x_2471_: *mut leanh::LeanObject,
    mut v_x_2472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2474_: u64 = 0;
    let mut v___x_2475_: usize = 0;
    let mut v___x_2476_: usize = 0;
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: u64 = 0;
    let mut v_hash_2479_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2471_) == 0 {
                    v___x_2478_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2474_ = v___x_2478_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2479_ = leanh::lean_ctor_get_uint64(
                        v_x_2471_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2474_ = v_hash_2479_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2475_ = lean_uint64_to_usize(v___y_2474_);
                v___x_2476_ = 1usize;
                v___x_2477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2470_, v___x_2475_, v___x_2476_, v_x_2471_, v_x_2472_);
                return v___x_2477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(
    mut v_a_2480_: *mut leanh::LeanObject,
    mut v_x_2481_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2482_: u8 = 0;
    let mut v_key_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2481_) == 0 {
                    v___x_2482_ = 0;
                    return v___x_2482_;
                } else {
                    v_key_2483_ = leanh::lean_ctor_get(v_x_2481_, 0);
                    v_tail_2484_ = leanh::lean_ctor_get(v_x_2481_, 2);
                    v___x_2485_ = lean_name_eq(v_key_2483_, v_a_2480_);
                    if v___x_2485_ == 0 {
                        v_x_2481_ = v_tail_2484_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2485_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_2487_: *mut leanh::LeanObject,
    mut v_x_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2489_: u8 = 0;
    let mut v_r_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2489_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_2487_, v_x_2488_);
    leanh::lean_dec(v_x_2488_);
    leanh::lean_dec(v_a_2487_);
    v_r_2490_ = leanh::lean_box((v_res_2489_) as usize);
    return v_r_2490_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(
    mut v_a_2491_: *mut leanh::LeanObject,
    mut v_b_2492_: *mut leanh::LeanObject,
    mut v_x_2493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___x_2500_: u8 = 0;
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2493_) == 0 {
                    leanh::lean_dec(v_b_2492_);
                    leanh::lean_dec(v_a_2491_);
                    return v_x_2493_;
                } else {
                    v_key_2494_ = leanh::lean_ctor_get(v_x_2493_, 0);
                    v_value_2495_ = leanh::lean_ctor_get(v_x_2493_, 1);
                    v_tail_2496_ = leanh::lean_ctor_get(v_x_2493_, 2);
                    v_isSharedCheck_2508_ = (!leanh::lean_is_exclusive(v_x_2493_)) as u8;
                    if v_isSharedCheck_2508_ == 0 {
                        v___x_2498_ = v_x_2493_;
                        v_isShared_2499_ = v_isSharedCheck_2508_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2496_);
                        leanh::lean_inc(v_value_2495_);
                        leanh::lean_inc(v_key_2494_);
                        leanh::lean_dec(v_x_2493_);
                        v___x_2498_ = leanh::lean_box(0);
                        v_isShared_2499_ = v_isSharedCheck_2508_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2500_ = lean_name_eq(v_key_2494_, v_a_2491_);
                if v___x_2500_ == 0 {
                    v___x_2501_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_a_2491_, v_b_2492_, v_tail_2496_);
                    if v_isShared_2499_ == 0 {
                        leanh::lean_ctor_set(v___x_2498_, 2, v___x_2501_);
                        v___x_2503_ = v___x_2498_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2504_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_key_2494_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_value_2495_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2504_, 2, v___x_2501_);
                        v___x_2503_ = v_reuseFailAlloc_2504_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_2495_);
                    leanh::lean_dec(v_key_2494_);
                    if v_isShared_2499_ == 0 {
                        leanh::lean_ctor_set(v___x_2498_, 1, v_b_2492_);
                        leanh::lean_ctor_set(v___x_2498_, 0, v_a_2491_);
                        v___x_2506_ = v___x_2498_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2507_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2491_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_b_2492_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 2, v_tail_2496_);
                        v___x_2506_ = v_reuseFailAlloc_2507_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2503_;
            }
            3 => {
                return v___x_2506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7_spec__9___redArg(
    mut v_x_2509_: *mut leanh::LeanObject,
    mut v_x_2510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: u64 = 0;
    let mut v___x_2520_: u64 = 0;
    let mut v___x_2521_: u64 = 0;
    let mut v_fold_2522_: u64 = 0;
    let mut v___x_2523_: u64 = 0;
    let mut v___x_2524_: u64 = 0;
    let mut v___x_2525_: u64 = 0;
    let mut v___x_2526_: usize = 0;
    let mut v___x_2527_: usize = 0;
    let mut v___x_2528_: usize = 0;
    let mut v___x_2529_: usize = 0;
    let mut v___x_2530_: usize = 0;
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: u64 = 0;
    let mut v_hash_2538_: u64 = 0;
    let mut v_isSharedCheck_2539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2510_) == 0 {
                    return v_x_2509_;
                } else {
                    v_key_2511_ = leanh::lean_ctor_get(v_x_2510_, 0);
                    v_value_2512_ = leanh::lean_ctor_get(v_x_2510_, 1);
                    v_tail_2513_ = leanh::lean_ctor_get(v_x_2510_, 2);
                    v_isSharedCheck_2539_ = (!leanh::lean_is_exclusive(v_x_2510_)) as u8;
                    if v_isSharedCheck_2539_ == 0 {
                        v___x_2515_ = v_x_2510_;
                        v_isShared_2516_ = v_isSharedCheck_2539_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2513_);
                        leanh::lean_inc(v_value_2512_);
                        leanh::lean_inc(v_key_2511_);
                        leanh::lean_dec(v_x_2510_);
                        v___x_2515_ = leanh::lean_box(0);
                        v_isShared_2516_ = v_isSharedCheck_2539_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2517_ = lean_array_get_size(v_x_2509_);
                if leanh::lean_obj_tag(v_key_2511_) == 0 {
                    v___x_2537_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2519_ = v___x_2537_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2538_ = leanh::lean_ctor_get_uint64(
                        v_key_2511_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2519_ = v_hash_2538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2520_ = 32u64;
                v___x_2521_ = lean_uint64_shift_right(v___y_2519_, v___x_2520_);
                v_fold_2522_ = lean_uint64_xor(v___y_2519_, v___x_2521_);
                v___x_2523_ = 16u64;
                v___x_2524_ = lean_uint64_shift_right(v_fold_2522_, v___x_2523_);
                v___x_2525_ = lean_uint64_xor(v_fold_2522_, v___x_2524_);
                v___x_2526_ = lean_uint64_to_usize(v___x_2525_);
                v___x_2527_ = lean_usize_of_nat(v___x_2517_);
                v___x_2528_ = 1usize;
                v___x_2529_ = lean_usize_sub(v___x_2527_, v___x_2528_);
                v___x_2530_ = lean_usize_land(v___x_2526_, v___x_2529_);
                v___x_2531_ = lean_array_uget_borrowed(v_x_2509_, v___x_2530_);
                leanh::lean_inc(v___x_2531_);
                if v_isShared_2516_ == 0 {
                    leanh::lean_ctor_set(v___x_2515_, 2, v___x_2531_);
                    v___x_2533_ = v___x_2515_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_key_2511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_value_2512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 2, v___x_2531_);
                    v___x_2533_ = v_reuseFailAlloc_2536_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2534_ = lean_array_uset(v_x_2509_, v___x_2530_, v___x_2533_);
                v_x_2509_ = v___x_2534_;
                v_x_2510_ = v_tail_2513_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7___redArg(
    mut v_i_2540_: *mut leanh::LeanObject,
    mut v_source_2541_: *mut leanh::LeanObject,
    mut v_target_2542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: u8 = 0;
    let mut v_es_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2543_ = lean_array_get_size(v_source_2541_);
                v___x_2544_ = lean_nat_dec_lt(v_i_2540_, v___x_2543_);
                if v___x_2544_ == 0 {
                    leanh::lean_dec_ref(v_source_2541_);
                    leanh::lean_dec(v_i_2540_);
                    return v_target_2542_;
                } else {
                    v_es_2545_ = lean_array_fget(v_source_2541_, v_i_2540_);
                    v___x_2546_ = leanh::lean_box(0);
                    v_source_2547_ = lean_array_fset(v_source_2541_, v_i_2540_, v___x_2546_);
                    v_target_2548_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_2542_, v_es_2545_);
                    v___x_2549_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2550_ = lean_nat_add(v_i_2540_, v___x_2549_);
                    leanh::lean_dec(v_i_2540_);
                    v_i_2540_ = v___x_2550_;
                    v_source_2541_ = v_source_2547_;
                    v_target_2542_ = v_target_2548_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4___redArg(
    mut v_data_2552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2553_ = lean_array_get_size(v_data_2552_);
    v___x_2554_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2555_ = lean_nat_mul(v___x_2553_, v___x_2554_);
    v___x_2556_ = leanh::lean_unsigned_to_nat(0);
    v___x_2557_ = leanh::lean_box(0);
    v___x_2558_ = lean_mk_array(v_nbuckets_2555_, v___x_2557_);
    v___x_2559_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7___redArg(v___x_2556_, v_data_2552_, v___x_2558_);
    return v___x_2559_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_m_2560_: *mut leanh::LeanObject,
    mut v_a_2561_: *mut leanh::LeanObject,
    mut v_b_2562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2570_: u64 = 0;
    let mut v___x_2571_: u64 = 0;
    let mut v___x_2572_: u64 = 0;
    let mut v_fold_2573_: u64 = 0;
    let mut v___x_2574_: u64 = 0;
    let mut v___x_2575_: u64 = 0;
    let mut v___x_2576_: u64 = 0;
    let mut v___x_2577_: usize = 0;
    let mut v___x_2578_: usize = 0;
    let mut v___x_2579_: usize = 0;
    let mut v___x_2580_: usize = 0;
    let mut v___x_2581_: usize = 0;
    let mut v_bkt_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v_val_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u64 = 0;
    let mut v_hash_2609_: u64 = 0;
    let mut v_isSharedCheck_2610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2563_ = leanh::lean_ctor_get(v_m_2560_, 0);
                v_buckets_2564_ = leanh::lean_ctor_get(v_m_2560_, 1);
                v_isSharedCheck_2610_ = (!leanh::lean_is_exclusive(v_m_2560_)) as u8;
                if v_isSharedCheck_2610_ == 0 {
                    v___x_2566_ = v_m_2560_;
                    v_isShared_2567_ = v_isSharedCheck_2610_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2564_);
                    leanh::lean_inc(v_size_2563_);
                    leanh::lean_dec(v_m_2560_);
                    v___x_2566_ = leanh::lean_box(0);
                    v_isShared_2567_ = v_isSharedCheck_2610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2568_ = lean_array_get_size(v_buckets_2564_);
                if leanh::lean_obj_tag(v_a_2561_) == 0 {
                    v___x_2608_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2570_ = v___x_2608_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2609_ = leanh::lean_ctor_get_uint64(
                        v_a_2561_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2570_ = v_hash_2609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2571_ = 32u64;
                v___x_2572_ = lean_uint64_shift_right(v___y_2570_, v___x_2571_);
                v_fold_2573_ = lean_uint64_xor(v___y_2570_, v___x_2572_);
                v___x_2574_ = 16u64;
                v___x_2575_ = lean_uint64_shift_right(v_fold_2573_, v___x_2574_);
                v___x_2576_ = lean_uint64_xor(v_fold_2573_, v___x_2575_);
                v___x_2577_ = lean_uint64_to_usize(v___x_2576_);
                v___x_2578_ = lean_usize_of_nat(v___x_2568_);
                v___x_2579_ = 1usize;
                v___x_2580_ = lean_usize_sub(v___x_2578_, v___x_2579_);
                v___x_2581_ = lean_usize_land(v___x_2577_, v___x_2580_);
                v_bkt_2582_ = lean_array_uget_borrowed(v_buckets_2564_, v___x_2581_);
                v___x_2583_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_2561_, v_bkt_2582_);
                if v___x_2583_ == 0 {
                    v___x_2584_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2585_ = lean_nat_add(v_size_2563_, v___x_2584_);
                    leanh::lean_dec(v_size_2563_);
                    leanh::lean_inc(v_bkt_2582_);
                    v___x_2586_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2586_, 0, v_a_2561_);
                    leanh::lean_ctor_set(v___x_2586_, 1, v_b_2562_);
                    leanh::lean_ctor_set(v___x_2586_, 2, v_bkt_2582_);
                    v_buckets_x27_2587_ =
                        lean_array_uset(v_buckets_2564_, v___x_2581_, v___x_2586_);
                    v___x_2588_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2589_ = lean_nat_mul(v_size_x27_2585_, v___x_2588_);
                    v___x_2590_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2591_ = lean_nat_div(v___x_2589_, v___x_2590_);
                    leanh::lean_dec(v___x_2589_);
                    v___x_2592_ = lean_array_get_size(v_buckets_x27_2587_);
                    v___x_2593_ = lean_nat_dec_le(v___x_2591_, v___x_2592_);
                    leanh::lean_dec(v___x_2591_);
                    if v___x_2593_ == 0 {
                        v_val_2594_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4___redArg(v_buckets_x27_2587_);
                        if v_isShared_2567_ == 0 {
                            leanh::lean_ctor_set(v___x_2566_, 1, v_val_2594_);
                            leanh::lean_ctor_set(v___x_2566_, 0, v_size_x27_2585_);
                            v___x_2596_ = v___x_2566_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2597_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2597_,
                                0,
                                v_size_x27_2585_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_val_2594_);
                            v___x_2596_ = v_reuseFailAlloc_2597_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_2567_ == 0 {
                            leanh::lean_ctor_set(v___x_2566_, 1, v_buckets_x27_2587_);
                            leanh::lean_ctor_set(v___x_2566_, 0, v_size_x27_2585_);
                            v___x_2599_ = v___x_2566_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2600_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2600_,
                                0,
                                v_size_x27_2585_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2600_,
                                1,
                                v_buckets_x27_2587_,
                            );
                            v___x_2599_ = v_reuseFailAlloc_2600_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_2582_);
                    v___x_2601_ = leanh::lean_box(0);
                    v_buckets_x27_2602_ =
                        lean_array_uset(v_buckets_2564_, v___x_2581_, v___x_2601_);
                    v___x_2603_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_a_2561_, v_b_2562_, v_bkt_2582_);
                    v___x_2604_ = lean_array_uset(v_buckets_x27_2602_, v___x_2581_, v___x_2603_);
                    if v_isShared_2567_ == 0 {
                        leanh::lean_ctor_set(v___x_2566_, 1, v___x_2604_);
                        v___x_2606_ = v___x_2566_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2607_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_size_2563_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2607_, 1, v___x_2604_);
                        v___x_2606_ = v_reuseFailAlloc_2607_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2596_;
            }
            4 => {
                return v___x_2599_;
            }
            5 => {
                return v___x_2606_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0___redArg(
    mut v_x_2611_: *mut leanh::LeanObject,
    mut v_x_2612_: *mut leanh::LeanObject,
    mut v_x_2613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_2614_: u8 = 0;
    let mut v_map_u2081_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2619_: u8 = 0;
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut v_map_u2081_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_2614_ = leanh::lean_ctor_get_uint8(
                    v_x_2611_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_2614_ == 0 {
                    v_map_u2081_2615_ = leanh::lean_ctor_get(v_x_2611_, 0);
                    v_map_u2082_2616_ = leanh::lean_ctor_get(v_x_2611_, 1);
                    v_isSharedCheck_2624_ = (!leanh::lean_is_exclusive(v_x_2611_)) as u8;
                    if v_isSharedCheck_2624_ == 0 {
                        v___x_2618_ = v_x_2611_;
                        v_isShared_2619_ = v_isSharedCheck_2624_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_2616_);
                        leanh::lean_inc(v_map_u2081_2615_);
                        leanh::lean_dec(v_x_2611_);
                        v___x_2618_ = leanh::lean_box(0);
                        v_isShared_2619_ = v_isSharedCheck_2624_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_2625_ = leanh::lean_ctor_get(v_x_2611_, 0);
                    v_map_u2082_2626_ = leanh::lean_ctor_get(v_x_2611_, 1);
                    v_isSharedCheck_2634_ = (!leanh::lean_is_exclusive(v_x_2611_)) as u8;
                    if v_isSharedCheck_2634_ == 0 {
                        v___x_2628_ = v_x_2611_;
                        v_isShared_2629_ = v_isSharedCheck_2634_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_2626_);
                        leanh::lean_inc(v_map_u2081_2625_);
                        leanh::lean_dec(v_x_2611_);
                        v___x_2628_ = leanh::lean_box(0);
                        v_isShared_2629_ = v_isSharedCheck_2634_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2620_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_u2082_2616_, v_x_2612_, v_x_2613_);
                if v_isShared_2619_ == 0 {
                    leanh::lean_ctor_set(v___x_2618_, 1, v___x_2620_);
                    v___x_2622_ = v___x_2618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2623_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_map_u2081_2615_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 1, v___x_2620_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2623_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_2614_,
                    );
                    v___x_2622_ = v_reuseFailAlloc_2623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2622_;
            }
            3 => {
                v___x_2630_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1___redArg(v_map_u2081_2625_, v_x_2612_, v_x_2613_);
                if v_isShared_2629_ == 0 {
                    leanh::lean_ctor_set(v___x_2628_, 0, v___x_2630_);
                    v___x_2632_ = v___x_2628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_map_u2082_2626_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2633_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_2614_,
                    );
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_(
    mut v_x_2635_: *mut leanh::LeanObject,
    mut v_e_2636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_thmNames_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2641_: u8 = 0;
    let mut v_fromDeclName_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_thmName_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2637_ = leanh::lean_ctor_get(v_x_2635_, 0);
                v_thmNames_2638_ = leanh::lean_ctor_get(v_x_2635_, 1);
                v_isSharedCheck_2650_ = (!leanh::lean_is_exclusive(v_x_2635_)) as u8;
                if v_isSharedCheck_2650_ == 0 {
                    v___x_2640_ = v_x_2635_;
                    v_isShared_2641_ = v_isSharedCheck_2650_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_thmNames_2638_);
                    leanh::lean_inc(v_map_2637_);
                    leanh::lean_dec(v_x_2635_);
                    v___x_2640_ = leanh::lean_box(0);
                    v_isShared_2641_ = v_isSharedCheck_2650_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fromDeclName_2642_ = leanh::lean_ctor_get(v_e_2636_, 0);
                leanh::lean_inc(v_fromDeclName_2642_);
                v_thmName_2643_ = leanh::lean_ctor_get(v_e_2636_, 2);
                leanh::lean_inc(v_thmName_2643_);
                v___x_2644_ = l_Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0___redArg(v_map_2637_, v_fromDeclName_2642_, v_e_2636_);
                v___x_2645_ = leanh::lean_box(0);
                v___x_2646_ = l_Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0___redArg(v_thmNames_2638_, v_thmName_2643_, v___x_2645_);
                if v_isShared_2641_ == 0 {
                    leanh::lean_ctor_set(v___x_2640_, 1, v___x_2646_);
                    leanh::lean_ctor_set(v___x_2640_, 0, v___x_2644_);
                    v___x_2648_ = v___x_2640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2649_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___x_2646_);
                    v___x_2648_ = v_reuseFailAlloc_2649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2663_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_;
    v___f_2664_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_;
    v___x_2665_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5,
    );
    v___f_2666_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_;
    v___x_2667_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_;
    v___x_2668_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2668_, 0, v___x_2667_);
    leanh::lean_ctor_set(v___x_2668_, 1, v___f_2666_);
    leanh::lean_ctor_set(v___x_2668_, 2, v___x_2665_);
    leanh::lean_ctor_set(v___x_2668_, 3, v___f_2664_);
    leanh::lean_ctor_set(v___x_2668_, 4, v___f_2663_);
    return v___x_2668_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2670_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_);
    v___x_2671_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2670_);
    return v___x_2671_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2____boxed(
    mut v_a_2672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2673_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_();
    return v_res_2673_;
}
pub unsafe fn l_Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_2674_: *mut leanh::LeanObject,
    mut v_x_2675_: *mut leanh::LeanObject,
    mut v_x_2676_: *mut leanh::LeanObject,
    mut v_x_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2678_ = l_Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0___redArg(v_x_2675_, v_x_2676_, v_x_2677_);
    return v___x_2678_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_2679_: *mut leanh::LeanObject,
    mut v_x_2680_: *mut leanh::LeanObject,
    mut v_x_2681_: *mut leanh::LeanObject,
    mut v_x_2682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2680_, v_x_2681_, v_x_2682_);
    return v___x_2683_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_2684_: *mut leanh::LeanObject,
    mut v_m_2685_: *mut leanh::LeanObject,
    mut v_a_2686_: *mut leanh::LeanObject,
    mut v_b_2687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2688_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1___redArg(v_m_2685_, v_a_2686_, v_b_2687_);
    return v___x_2688_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b2_2689_: *mut leanh::LeanObject,
    mut v_x_2690_: *mut leanh::LeanObject,
    mut v_x_2691_: usize,
    mut v_x_2692_: usize,
    mut v_x_2693_: *mut leanh::LeanObject,
    mut v_x_2694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2695_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2690_, v_x_2691_, v_x_2692_, v_x_2693_, v_x_2694_);
    return v___x_2695_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2696_: *mut leanh::LeanObject,
    mut v_x_2697_: *mut leanh::LeanObject,
    mut v_x_2698_: *mut leanh::LeanObject,
    mut v_x_2699_: *mut leanh::LeanObject,
    mut v_x_2700_: *mut leanh::LeanObject,
    mut v_x_2701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1461__boxed_2702_: usize = 0;
    let mut v_x_1462__boxed_2703_: usize = 0;
    let mut v_res_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1461__boxed_2702_ = leanh::lean_unbox_usize(v_x_2698_);
    leanh::lean_dec(v_x_2698_);
    v_x_1462__boxed_2703_ = leanh::lean_unbox_usize(v_x_2699_);
    leanh::lean_dec(v_x_2699_);
    v_res_2704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2696_, v_x_2697_, v_x_1461__boxed_2702_, v_x_1462__boxed_2703_, v_x_2700_, v_x_2701_);
    return v_res_2704_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3(
    mut v_00_u03b2_2705_: *mut leanh::LeanObject,
    mut v_a_2706_: *mut leanh::LeanObject,
    mut v_x_2707_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2708_: u8 = 0;
    v___x_2708_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_2706_, v_x_2707_);
    return v___x_2708_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2709_: *mut leanh::LeanObject,
    mut v_a_2710_: *mut leanh::LeanObject,
    mut v_x_2711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2712_: u8 = 0;
    let mut v_r_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2712_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_2709_, v_a_2710_, v_x_2711_);
    leanh::lean_dec(v_x_2711_);
    leanh::lean_dec(v_a_2710_);
    v_r_2713_ = leanh::lean_box((v_res_2712_) as usize);
    return v_r_2713_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4(
    mut v_00_u03b2_2714_: *mut leanh::LeanObject,
    mut v_data_2715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2716_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4___redArg(v_data_2715_);
    return v___x_2716_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__5(
    mut v_00_u03b2_2717_: *mut leanh::LeanObject,
    mut v_a_2718_: *mut leanh::LeanObject,
    mut v_b_2719_: *mut leanh::LeanObject,
    mut v_x_2720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_a_2718_, v_b_2719_, v_x_2720_);
    return v___x_2721_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2722_: *mut leanh::LeanObject,
    mut v_n_2723_: *mut leanh::LeanObject,
    mut v_k_2724_: *mut leanh::LeanObject,
    mut v_v_2725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2726_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_n_2723_, v_k_2724_, v_v_2725_);
    return v___x_2726_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2727_: *mut leanh::LeanObject,
    mut v_depth_2728_: usize,
    mut v_keys_2729_: *mut leanh::LeanObject,
    mut v_vals_2730_: *mut leanh::LeanObject,
    mut v_heq_2731_: *mut leanh::LeanObject,
    mut v_i_2732_: *mut leanh::LeanObject,
    mut v_entries_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2734_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2728_, v_keys_2729_, v_vals_2730_, v_i_2732_, v_entries_2733_);
    return v___x_2734_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2735_: *mut leanh::LeanObject,
    mut v_depth_2736_: *mut leanh::LeanObject,
    mut v_keys_2737_: *mut leanh::LeanObject,
    mut v_vals_2738_: *mut leanh::LeanObject,
    mut v_heq_2739_: *mut leanh::LeanObject,
    mut v_i_2740_: *mut leanh::LeanObject,
    mut v_entries_2741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2742_: usize = 0;
    let mut v_res_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2742_ = leanh::lean_unbox_usize(v_depth_2736_);
    leanh::lean_dec(v_depth_2736_);
    v_res_2743_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2735_, v_depth_boxed_2742_, v_keys_2737_, v_vals_2738_, v_heq_2739_, v_i_2740_, v_entries_2741_);
    leanh::lean_dec_ref(v_vals_2738_);
    leanh::lean_dec_ref(v_keys_2737_);
    return v_res_2743_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7(
    mut v_00_u03b2_2744_: *mut leanh::LeanObject,
    mut v_i_2745_: *mut leanh::LeanObject,
    mut v_source_2746_: *mut leanh::LeanObject,
    mut v_target_2747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7___redArg(v_i_2745_, v_source_2746_, v_target_2747_);
    return v___x_2748_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2749_: *mut leanh::LeanObject,
    mut v_x_2750_: *mut leanh::LeanObject,
    mut v_x_2751_: *mut leanh::LeanObject,
    mut v_x_2752_: *mut leanh::LeanObject,
    mut v_x_2753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2750_, v_x_2751_, v_x_2752_, v_x_2753_);
    return v___x_2754_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7_spec__9(
    mut v_00_u03b2_2755_: *mut leanh::LeanObject,
    mut v_x_2756_: *mut leanh::LeanObject,
    mut v_x_2757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2758_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_2756_, v_x_2757_);
    return v___x_2758_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3(
    mut v_a_2762_: *mut leanh::LeanObject,
    mut v_a_2763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2762_) == 0 {
                    v___x_2764_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2764_, 0, v_a_2763_);
                    return v___x_2764_;
                } else {
                    leanh::lean_dec_ref(v_a_2763_);
                    v_key_2765_ = leanh::lean_ctor_get(v_a_2762_, 0);
                    v_tail_2766_ = leanh::lean_ctor_get(v_a_2762_, 2);
                    v___x_2767_ = leanh::lean_box(0);
                    v___x_2768_ = l_Lean_Level_isParam(v_key_2765_);
                    if v___x_2768_ == 0 {
                        v___x_2769_ = leanh::lean_box((v___x_2768_) as usize);
                        v___x_2770_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2770_, 0, v___x_2769_);
                        v___x_2771_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2771_, 0, v___x_2770_);
                        leanh::lean_ctor_set(v___x_2771_, 1, v___x_2767_);
                        v___x_2772_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2772_, 0, v___x_2771_);
                        return v___x_2772_;
                    } else {
                        v___x_2773_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___closed__0;
                        v_a_2762_ = v_tail_2766_;
                        v_a_2763_ = v___x_2773_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___boxed(
    mut v_a_2775_: *mut leanh::LeanObject,
    mut v_a_2776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2777_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3(v_a_2775_, v_a_2776_);
    leanh::lean_dec(v_a_2775_);
    return v_res_2777_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__4(
    mut v_as_2778_: *mut leanh::LeanObject,
    mut v_sz_2779_: usize,
    mut v_i_2780_: usize,
    mut v_b_2781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2782_: u8 = 0;
    let mut v_a_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: usize = 0;
    let mut v___x_2788_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2782_ = lean_usize_dec_lt(v_i_2780_, v_sz_2779_);
                if v___x_2782_ == 0 {
                    return v_b_2781_;
                } else {
                    v_a_2783_ = lean_array_uget_borrowed(v_as_2778_, v_i_2780_);
                    v___x_2784_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3(v_a_2783_, v_b_2781_);
                    if leanh::lean_obj_tag(v___x_2784_) == 0 {
                        v_a_2785_ = leanh::lean_ctor_get(v___x_2784_, 0);
                        leanh::lean_inc(v_a_2785_);
                        leanh::lean_dec_ref_known(v___x_2784_, 1);
                        return v_a_2785_;
                    } else {
                        v_a_2786_ = leanh::lean_ctor_get(v___x_2784_, 0);
                        leanh::lean_inc(v_a_2786_);
                        leanh::lean_dec_ref_known(v___x_2784_, 1);
                        v___x_2787_ = 1usize;
                        v___x_2788_ = lean_usize_add(v_i_2780_, v___x_2787_);
                        v_i_2780_ = v___x_2788_;
                        v_b_2781_ = v_a_2786_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__4___boxed(
    mut v_as_2790_: *mut leanh::LeanObject,
    mut v_sz_2791_: *mut leanh::LeanObject,
    mut v_i_2792_: *mut leanh::LeanObject,
    mut v_b_2793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2794_: usize = 0;
    let mut v_i_boxed_2795_: usize = 0;
    let mut v_res_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2794_ = leanh::lean_unbox_usize(v_sz_2791_);
    leanh::lean_dec(v_sz_2791_);
    v_i_boxed_2795_ = leanh::lean_unbox_usize(v_i_2792_);
    leanh::lean_dec(v_i_2792_);
    v_res_2796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__4(v_as_2790_, v_sz_boxed_2794_, v_i_boxed_2795_, v_b_2793_);
    leanh::lean_dec_ref(v_as_2790_);
    return v_res_2796_;
}
pub unsafe fn l_List_beq___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__1(
    mut v_x_2797_: *mut leanh::LeanObject,
    mut v_x_2798_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2799_: u8 = 0;
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: u8 = 0;
    let mut v_head_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2797_) == 0 {
                    if leanh::lean_obj_tag(v_x_2798_) == 0 {
                        v___x_2799_ = 1;
                        return v___x_2799_;
                    } else {
                        v___x_2800_ = 0;
                        return v___x_2800_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_2798_) == 0 {
                        v___x_2801_ = 0;
                        return v___x_2801_;
                    } else {
                        v_head_2802_ = leanh::lean_ctor_get(v_x_2797_, 0);
                        v_tail_2803_ = leanh::lean_ctor_get(v_x_2797_, 1);
                        v_head_2804_ = leanh::lean_ctor_get(v_x_2798_, 0);
                        v_tail_2805_ = leanh::lean_ctor_get(v_x_2798_, 1);
                        v___x_2806_ = lean_level_eq(v_head_2802_, v_head_2804_);
                        if v___x_2806_ == 0 {
                            return v___x_2806_;
                        } else {
                            v_x_2797_ = v_tail_2803_;
                            v_x_2798_ = v_tail_2805_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__1___boxed(
    mut v_x_2808_: *mut leanh::LeanObject,
    mut v_x_2809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2810_: u8 = 0;
    let mut v_r_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2810_ = l_List_beq___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__1(v_x_2808_, v_x_2809_);
    leanh::lean_dec(v_x_2809_);
    leanh::lean_dec(v_x_2808_);
    v_r_2811_ = leanh::lean_box((v_res_2810_) as usize);
    return v_r_2811_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2812_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2812_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2813_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0);
    v___x_2814_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2814_, 0, v___x_2813_);
    return v___x_2814_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2815_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1);
    v___x_2816_ = leanh::lean_unsigned_to_nat(0);
    v___x_2817_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2817_, 0, v___x_2816_);
    leanh::lean_ctor_set(v___x_2817_, 1, v___x_2816_);
    leanh::lean_ctor_set(v___x_2817_, 2, v___x_2816_);
    leanh::lean_ctor_set(v___x_2817_, 3, v___x_2816_);
    leanh::lean_ctor_set(v___x_2817_, 4, v___x_2815_);
    leanh::lean_ctor_set(v___x_2817_, 5, v___x_2815_);
    leanh::lean_ctor_set(v___x_2817_, 6, v___x_2815_);
    leanh::lean_ctor_set(v___x_2817_, 7, v___x_2815_);
    leanh::lean_ctor_set(v___x_2817_, 8, v___x_2815_);
    leanh::lean_ctor_set(v___x_2817_, 9, v___x_2815_);
    return v___x_2817_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2818_ = leanh::lean_unsigned_to_nat(32);
    v___x_2819_ = lean_mk_empty_array_with_capacity(v___x_2818_);
    v___x_2820_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2820_, 0, v___x_2819_);
    return v___x_2820_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2821_: usize = 0;
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2821_ = 5usize;
    v___x_2822_ = leanh::lean_unsigned_to_nat(0);
    v___x_2823_ = leanh::lean_unsigned_to_nat(32);
    v___x_2824_ = lean_mk_empty_array_with_capacity(v___x_2823_);
    v___x_2825_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3);
    v___x_2826_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2826_, 0, v___x_2825_);
    leanh::lean_ctor_set(v___x_2826_, 1, v___x_2824_);
    leanh::lean_ctor_set(v___x_2826_, 2, v___x_2822_);
    leanh::lean_ctor_set(v___x_2826_, 3, v___x_2822_);
    leanh::lean_ctor_set_usize(v___x_2826_, 4, v___x_2821_);
    return v___x_2826_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2827_ = leanh::lean_box(1);
    v___x_2828_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4);
    v___x_2829_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1);
    v___x_2830_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2830_, 0, v___x_2829_);
    leanh::lean_ctor_set(v___x_2830_, 1, v___x_2828_);
    leanh::lean_ctor_set(v___x_2830_, 2, v___x_2827_);
    return v___x_2830_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2832_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__6;
    v___x_2833_ = l_Lean_stringToMessageData(v___x_2832_);
    return v___x_2833_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2835_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__8;
    v___x_2836_ = l_Lean_stringToMessageData(v___x_2835_);
    return v___x_2836_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2838_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__10;
    v___x_2839_ = l_Lean_stringToMessageData(v___x_2838_);
    return v___x_2839_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__12;
    v___x_2842_ = l_Lean_stringToMessageData(v___x_2841_);
    return v___x_2842_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__14;
    v___x_2845_ = l_Lean_stringToMessageData(v___x_2844_);
    return v___x_2845_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2847_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__16;
    v___x_2848_ = l_Lean_stringToMessageData(v___x_2847_);
    return v___x_2848_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2850_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__18;
    v___x_2851_ = l_Lean_stringToMessageData(v___x_2850_);
    return v___x_2851_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg(
    mut v_msg_2852_: *mut leanh::LeanObject,
    mut v_declHint_2853_: *mut leanh::LeanObject,
    mut v___y_2854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: u8 = 0;
    let mut v_isExporting_2859_: u8 = 0;
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: u8 = 0;
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2856_ = lean_st_ref_get(v___y_2854_);
                v_env_2857_ = leanh::lean_ctor_get(v___x_2856_, 0);
                leanh::lean_inc_ref(v_env_2857_);
                leanh::lean_dec(v___x_2856_);
                v___x_2858_ = l_Lean_Name_isAnonymous(v_declHint_2853_);
                if v___x_2858_ == 0 {
                    v_isExporting_2859_ = leanh::lean_ctor_get_uint8(
                        v_env_2857_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2859_ == 0 {
                        leanh::lean_dec_ref(v_env_2857_);
                        leanh::lean_dec(v_declHint_2853_);
                        v___x_2860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2860_, 0, v_msg_2852_);
                        return v___x_2860_;
                    } else {
                        leanh::lean_inc_ref(v_env_2857_);
                        v___x_2861_ = l_Lean_Environment_setExporting(v_env_2857_, v___x_2858_);
                        leanh::lean_inc(v_declHint_2853_);
                        leanh::lean_inc_ref(v___x_2861_);
                        v___x_2862_ = l_Lean_Environment_contains(
                            v___x_2861_,
                            v_declHint_2853_,
                            v_isExporting_2859_,
                        );
                        if v___x_2862_ == 0 {
                            leanh::lean_dec_ref(v___x_2861_);
                            leanh::lean_dec_ref(v_env_2857_);
                            leanh::lean_dec(v_declHint_2853_);
                            v___x_2863_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2863_, 0, v_msg_2852_);
                            return v___x_2863_;
                        } else {
                            v___x_2864_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2);
                            v___x_2865_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5);
                            v___x_2866_ = l_Lean_Options_empty;
                            v___x_2867_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_2867_, 0, v___x_2861_);
                            leanh::lean_ctor_set(v___x_2867_, 1, v___x_2864_);
                            leanh::lean_ctor_set(v___x_2867_, 2, v___x_2865_);
                            leanh::lean_ctor_set(v___x_2867_, 3, v___x_2866_);
                            leanh::lean_inc(v_declHint_2853_);
                            v___x_2868_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2853_, v___x_2858_);
                            v_c_2869_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_2869_, 0, v___x_2867_);
                            leanh::lean_ctor_set(v_c_2869_, 1, v___x_2868_);
                            v___x_2870_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2857_,
                                v_declHint_2853_,
                            );
                            if leanh::lean_obj_tag(v___x_2870_) == 0 {
                                leanh::lean_dec_ref(v_env_2857_);
                                leanh::lean_dec(v_declHint_2853_);
                                v___x_2871_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7);
                                v___x_2872_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2872_, 0, v___x_2871_);
                                leanh::lean_ctor_set(v___x_2872_, 1, v_c_2869_);
                                v___x_2873_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9);
                                v___x_2874_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2874_, 0, v___x_2872_);
                                leanh::lean_ctor_set(v___x_2874_, 1, v___x_2873_);
                                v___x_2875_ = l_Lean_MessageData_note(v___x_2874_);
                                v___x_2876_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2876_, 0, v_msg_2852_);
                                leanh::lean_ctor_set(v___x_2876_, 1, v___x_2875_);
                                v___x_2877_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2877_, 0, v___x_2876_);
                                return v___x_2877_;
                            } else {
                                v_val_2878_ = leanh::lean_ctor_get(v___x_2870_, 0);
                                v_isSharedCheck_2913_ =
                                    (!leanh::lean_is_exclusive(v___x_2870_)) as u8;
                                if v_isSharedCheck_2913_ == 0 {
                                    v___x_2880_ = v___x_2870_;
                                    v_isShared_2881_ = v_isSharedCheck_2913_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_2878_);
                                    leanh::lean_dec(v___x_2870_);
                                    v___x_2880_ = leanh::lean_box(0);
                                    v_isShared_2881_ = v_isSharedCheck_2913_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2857_);
                    leanh::lean_dec(v_declHint_2853_);
                    v___x_2914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2914_, 0, v_msg_2852_);
                    return v___x_2914_;
                }
            }
            1 => {
                v___x_2882_ = leanh::lean_box(0);
                v___x_2883_ = l_Lean_Environment_header(v_env_2857_);
                leanh::lean_dec_ref(v_env_2857_);
                v___x_2884_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2883_);
                v_mod_2885_ = lean_array_get(v___x_2882_, v___x_2884_, v_val_2878_);
                leanh::lean_dec(v_val_2878_);
                leanh::lean_dec_ref(v___x_2884_);
                v___x_2886_ = l_Lean_isPrivateName(v_declHint_2853_);
                leanh::lean_dec(v_declHint_2853_);
                if v___x_2886_ == 0 {
                    v___x_2887_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11);
                    v___x_2888_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2888_, 0, v___x_2887_);
                    leanh::lean_ctor_set(v___x_2888_, 1, v_c_2869_);
                    v___x_2889_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13);
                    v___x_2890_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2890_, 0, v___x_2888_);
                    leanh::lean_ctor_set(v___x_2890_, 1, v___x_2889_);
                    v___x_2891_ = l_Lean_MessageData_ofName(v_mod_2885_);
                    v___x_2892_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2892_, 0, v___x_2890_);
                    leanh::lean_ctor_set(v___x_2892_, 1, v___x_2891_);
                    v___x_2893_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15);
                    v___x_2894_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2894_, 0, v___x_2892_);
                    leanh::lean_ctor_set(v___x_2894_, 1, v___x_2893_);
                    v___x_2895_ = l_Lean_MessageData_note(v___x_2894_);
                    v___x_2896_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2896_, 0, v_msg_2852_);
                    leanh::lean_ctor_set(v___x_2896_, 1, v___x_2895_);
                    if v_isShared_2881_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2880_, 0);
                        leanh::lean_ctor_set(v___x_2880_, 0, v___x_2896_);
                        v___x_2898_ = v___x_2880_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2899_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
                        v___x_2898_ = v_reuseFailAlloc_2899_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2900_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7);
                    v___x_2901_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2901_, 0, v___x_2900_);
                    leanh::lean_ctor_set(v___x_2901_, 1, v_c_2869_);
                    v___x_2902_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17);
                    v___x_2903_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2903_, 0, v___x_2901_);
                    leanh::lean_ctor_set(v___x_2903_, 1, v___x_2902_);
                    v___x_2904_ = l_Lean_MessageData_ofName(v_mod_2885_);
                    v___x_2905_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2905_, 0, v___x_2903_);
                    leanh::lean_ctor_set(v___x_2905_, 1, v___x_2904_);
                    v___x_2906_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19);
                    v___x_2907_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2907_, 0, v___x_2905_);
                    leanh::lean_ctor_set(v___x_2907_, 1, v___x_2906_);
                    v___x_2908_ = l_Lean_MessageData_note(v___x_2907_);
                    v___x_2909_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2909_, 0, v_msg_2852_);
                    leanh::lean_ctor_set(v___x_2909_, 1, v___x_2908_);
                    if v_isShared_2881_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2880_, 0);
                        leanh::lean_ctor_set(v___x_2880_, 0, v___x_2909_);
                        v___x_2911_ = v___x_2880_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
                        v___x_2911_ = v_reuseFailAlloc_2912_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2898_;
            }
            3 => {
                return v___x_2911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___boxed(
    mut v_msg_2915_: *mut leanh::LeanObject,
    mut v_declHint_2916_: *mut leanh::LeanObject,
    mut v___y_2917_: *mut leanh::LeanObject,
    mut v___y_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2919_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg(v_msg_2915_, v_declHint_2916_, v___y_2917_);
    leanh::lean_dec(v___y_2917_);
    return v_res_2919_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9(
    mut v_msg_2920_: *mut leanh::LeanObject,
    mut v_declHint_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
    mut v___y_2923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2925_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg(v_msg_2920_, v_declHint_2921_, v___y_2923_);
                v_a_2926_ = leanh::lean_ctor_get(v___x_2925_, 0);
                v_isSharedCheck_2935_ = (!leanh::lean_is_exclusive(v___x_2925_)) as u8;
                if v_isSharedCheck_2935_ == 0 {
                    v___x_2928_ = v___x_2925_;
                    v_isShared_2929_ = v_isSharedCheck_2935_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2926_);
                    leanh::lean_dec(v___x_2925_);
                    v___x_2928_ = leanh::lean_box(0);
                    v_isShared_2929_ = v_isSharedCheck_2935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2930_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2931_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2931_, 0, v___x_2930_);
                leanh::lean_ctor_set(v___x_2931_, 1, v_a_2926_);
                if v_isShared_2929_ == 0 {
                    leanh::lean_ctor_set(v___x_2928_, 0, v___x_2931_);
                    v___x_2933_ = v___x_2928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
                    v___x_2933_ = v_reuseFailAlloc_2934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9___boxed(
    mut v_msg_2936_: *mut leanh::LeanObject,
    mut v_declHint_2937_: *mut leanh::LeanObject,
    mut v___y_2938_: *mut leanh::LeanObject,
    mut v___y_2939_: *mut leanh::LeanObject,
    mut v___y_2940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2941_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9(v_msg_2936_, v_declHint_2937_, v___y_2938_, v___y_2939_);
    leanh::lean_dec(v___y_2939_);
    leanh::lean_dec_ref(v___y_2938_);
    return v_res_2941_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(
    mut v_msgData_2942_: *mut leanh::LeanObject,
    mut v___y_2943_: *mut leanh::LeanObject,
    mut v___y_2944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2946_ = lean_st_ref_get(v___y_2944_);
    v_env_2947_ = leanh::lean_ctor_get(v___x_2946_, 0);
    leanh::lean_inc_ref(v_env_2947_);
    leanh::lean_dec(v___x_2946_);
    v_options_2948_ = leanh::lean_ctor_get(v___y_2943_, 2);
    v___x_2949_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2);
    v___x_2950_ = leanh::lean_unsigned_to_nat(32);
    v___x_2951_ = lean_mk_empty_array_with_capacity(v___x_2950_);
    leanh::lean_dec_ref(v___x_2951_);
    v___x_2952_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5);
    leanh::lean_inc_ref(v_options_2948_);
    v___x_2953_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2953_, 0, v_env_2947_);
    leanh::lean_ctor_set(v___x_2953_, 1, v___x_2949_);
    leanh::lean_ctor_set(v___x_2953_, 2, v___x_2952_);
    leanh::lean_ctor_set(v___x_2953_, 3, v_options_2948_);
    v___x_2954_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2954_, 0, v___x_2953_);
    leanh::lean_ctor_set(v___x_2954_, 1, v_msgData_2942_);
    v___x_2955_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2955_, 0, v___x_2954_);
    return v___x_2955_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16___boxed(
    mut v_msgData_2956_: *mut leanh::LeanObject,
    mut v___y_2957_: *mut leanh::LeanObject,
    mut v___y_2958_: *mut leanh::LeanObject,
    mut v___y_2959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2960_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v_msgData_2956_, v___y_2957_, v___y_2958_);
    leanh::lean_dec(v___y_2958_);
    leanh::lean_dec_ref(v___y_2957_);
    return v_res_2960_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(
    mut v_msg_2961_: *mut leanh::LeanObject,
    mut v___y_2962_: *mut leanh::LeanObject,
    mut v___y_2963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2970_: u8 = 0;
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2965_ = leanh::lean_ctor_get(v___y_2962_, 5);
                v___x_2966_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v_msg_2961_, v___y_2962_, v___y_2963_);
                v_a_2967_ = leanh::lean_ctor_get(v___x_2966_, 0);
                v_isSharedCheck_2975_ = (!leanh::lean_is_exclusive(v___x_2966_)) as u8;
                if v_isSharedCheck_2975_ == 0 {
                    v___x_2969_ = v___x_2966_;
                    v_isShared_2970_ = v_isSharedCheck_2975_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2967_);
                    leanh::lean_dec(v___x_2966_);
                    v___x_2969_ = leanh::lean_box(0);
                    v_isShared_2970_ = v_isSharedCheck_2975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2965_);
                v___x_2971_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2971_, 0, v_ref_2965_);
                leanh::lean_ctor_set(v___x_2971_, 1, v_a_2967_);
                if v_isShared_2970_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2969_, 1);
                    leanh::lean_ctor_set(v___x_2969_, 0, v___x_2971_);
                    v___x_2973_ = v___x_2969_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2974_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
                    v___x_2973_ = v_reuseFailAlloc_2974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg___boxed(
    mut v_msg_2976_: *mut leanh::LeanObject,
    mut v___y_2977_: *mut leanh::LeanObject,
    mut v___y_2978_: *mut leanh::LeanObject,
    mut v___y_2979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2980_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(v_msg_2976_, v___y_2977_, v___y_2978_);
    leanh::lean_dec(v___y_2978_);
    leanh::lean_dec_ref(v___y_2977_);
    return v_res_2980_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(
    mut v_ref_2981_: *mut leanh::LeanObject,
    mut v_msg_2982_: *mut leanh::LeanObject,
    mut v___y_2983_: *mut leanh::LeanObject,
    mut v___y_2984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2998_: u8 = 0;
    let mut v_cancelTk_x3f_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3000_: u8 = 0;
    let mut v_inheritedTraceOptions_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2986_ = leanh::lean_ctor_get(v___y_2983_, 0);
    v_fileMap_2987_ = leanh::lean_ctor_get(v___y_2983_, 1);
    v_options_2988_ = leanh::lean_ctor_get(v___y_2983_, 2);
    v_currRecDepth_2989_ = leanh::lean_ctor_get(v___y_2983_, 3);
    v_maxRecDepth_2990_ = leanh::lean_ctor_get(v___y_2983_, 4);
    v_ref_2991_ = leanh::lean_ctor_get(v___y_2983_, 5);
    v_currNamespace_2992_ = leanh::lean_ctor_get(v___y_2983_, 6);
    v_openDecls_2993_ = leanh::lean_ctor_get(v___y_2983_, 7);
    v_initHeartbeats_2994_ = leanh::lean_ctor_get(v___y_2983_, 8);
    v_maxHeartbeats_2995_ = leanh::lean_ctor_get(v___y_2983_, 9);
    v_quotContext_2996_ = leanh::lean_ctor_get(v___y_2983_, 10);
    v_currMacroScope_2997_ = leanh::lean_ctor_get(v___y_2983_, 11);
    v_diag_2998_ = leanh::lean_ctor_get_uint8(
        v___y_2983_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2999_ = leanh::lean_ctor_get(v___y_2983_, 12);
    v_suppressElabErrors_3000_ = leanh::lean_ctor_get_uint8(
        v___y_2983_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3001_ = leanh::lean_ctor_get(v___y_2983_, 13);
    v_ref_3002_ = l_Lean_replaceRef(v_ref_2981_, v_ref_2991_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3001_);
    leanh::lean_inc(v_cancelTk_x3f_2999_);
    leanh::lean_inc(v_currMacroScope_2997_);
    leanh::lean_inc(v_quotContext_2996_);
    leanh::lean_inc(v_maxHeartbeats_2995_);
    leanh::lean_inc(v_initHeartbeats_2994_);
    leanh::lean_inc(v_openDecls_2993_);
    leanh::lean_inc(v_currNamespace_2992_);
    leanh::lean_inc(v_maxRecDepth_2990_);
    leanh::lean_inc(v_currRecDepth_2989_);
    leanh::lean_inc_ref(v_options_2988_);
    leanh::lean_inc_ref(v_fileMap_2987_);
    leanh::lean_inc_ref(v_fileName_2986_);
    v___x_3003_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3003_, 0, v_fileName_2986_);
    leanh::lean_ctor_set(v___x_3003_, 1, v_fileMap_2987_);
    leanh::lean_ctor_set(v___x_3003_, 2, v_options_2988_);
    leanh::lean_ctor_set(v___x_3003_, 3, v_currRecDepth_2989_);
    leanh::lean_ctor_set(v___x_3003_, 4, v_maxRecDepth_2990_);
    leanh::lean_ctor_set(v___x_3003_, 5, v_ref_3002_);
    leanh::lean_ctor_set(v___x_3003_, 6, v_currNamespace_2992_);
    leanh::lean_ctor_set(v___x_3003_, 7, v_openDecls_2993_);
    leanh::lean_ctor_set(v___x_3003_, 8, v_initHeartbeats_2994_);
    leanh::lean_ctor_set(v___x_3003_, 9, v_maxHeartbeats_2995_);
    leanh::lean_ctor_set(v___x_3003_, 10, v_quotContext_2996_);
    leanh::lean_ctor_set(v___x_3003_, 11, v_currMacroScope_2997_);
    leanh::lean_ctor_set(v___x_3003_, 12, v_cancelTk_x3f_2999_);
    leanh::lean_ctor_set(v___x_3003_, 13, v_inheritedTraceOptions_3001_);
    leanh::lean_ctor_set_uint8(
        v___x_3003_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_2998_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3003_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3000_,
    );
    v___x_3004_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(v_msg_2982_, v___x_3003_, v___y_2984_);
    leanh::lean_dec_ref_known(v___x_3003_, 14);
    return v___x_3004_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___redArg___boxed(
    mut v_ref_3005_: *mut leanh::LeanObject,
    mut v_msg_3006_: *mut leanh::LeanObject,
    mut v___y_3007_: *mut leanh::LeanObject,
    mut v___y_3008_: *mut leanh::LeanObject,
    mut v___y_3009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3010_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_ref_3005_, v_msg_3006_, v___y_3007_, v___y_3008_);
    leanh::lean_dec(v___y_3008_);
    leanh::lean_dec_ref(v___y_3007_);
    leanh::lean_dec(v_ref_3005_);
    return v_res_3010_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___redArg(
    mut v_ref_3011_: *mut leanh::LeanObject,
    mut v_msg_3012_: *mut leanh::LeanObject,
    mut v_declHint_3013_: *mut leanh::LeanObject,
    mut v___y_3014_: *mut leanh::LeanObject,
    mut v___y_3015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3017_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9(v_msg_3012_, v_declHint_3013_, v___y_3014_, v___y_3015_);
    v_a_3018_ = leanh::lean_ctor_get(v___x_3017_, 0);
    leanh::lean_inc(v_a_3018_);
    leanh::lean_dec_ref(v___x_3017_);
    v___x_3019_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_ref_3011_, v_a_3018_, v___y_3014_, v___y_3015_);
    return v___x_3019_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___redArg___boxed(
    mut v_ref_3020_: *mut leanh::LeanObject,
    mut v_msg_3021_: *mut leanh::LeanObject,
    mut v_declHint_3022_: *mut leanh::LeanObject,
    mut v___y_3023_: *mut leanh::LeanObject,
    mut v___y_3024_: *mut leanh::LeanObject,
    mut v___y_3025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3026_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_3020_, v_msg_3021_, v_declHint_3022_, v___y_3023_, v___y_3024_);
    leanh::lean_dec(v___y_3024_);
    leanh::lean_dec_ref(v___y_3023_);
    leanh::lean_dec(v_ref_3020_);
    return v_res_3026_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3028_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_3029_ = l_Lean_stringToMessageData(v___x_3028_);
    return v___x_3029_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3031_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_3032_ = l_Lean_stringToMessageData(v___x_3031_);
    return v___x_3032_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_ref_3033_: *mut leanh::LeanObject,
    mut v_constName_3034_: *mut leanh::LeanObject,
    mut v___y_3035_: *mut leanh::LeanObject,
    mut v___y_3036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3038_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_3039_ = 0;
    leanh::lean_inc(v_constName_3034_);
    v___x_3040_ = l_Lean_MessageData_ofConstName(v_constName_3034_, v___x_3039_);
    v___x_3041_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3041_, 0, v___x_3038_);
    leanh::lean_ctor_set(v___x_3041_, 1, v___x_3040_);
    v___x_3042_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_3043_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3043_, 0, v___x_3041_);
    leanh::lean_ctor_set(v___x_3043_, 1, v___x_3042_);
    v___x_3044_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_3033_, v___x_3043_, v_constName_3034_, v___y_3035_, v___y_3036_);
    return v___x_3044_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_3045_: *mut leanh::LeanObject,
    mut v_constName_3046_: *mut leanh::LeanObject,
    mut v___y_3047_: *mut leanh::LeanObject,
    mut v___y_3048_: *mut leanh::LeanObject,
    mut v___y_3049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3050_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg(v_ref_3045_, v_constName_3046_, v___y_3047_, v___y_3048_);
    leanh::lean_dec(v___y_3048_);
    leanh::lean_dec_ref(v___y_3047_);
    leanh::lean_dec(v_ref_3045_);
    return v_res_3050_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg(
    mut v_constName_3051_: *mut leanh::LeanObject,
    mut v___y_3052_: *mut leanh::LeanObject,
    mut v___y_3053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3055_ = leanh::lean_ctor_get(v___y_3052_, 5);
    v___x_3056_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg(v_ref_3055_, v_constName_3051_, v___y_3052_, v___y_3053_);
    return v___x_3056_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_3057_: *mut leanh::LeanObject,
    mut v___y_3058_: *mut leanh::LeanObject,
    mut v___y_3059_: *mut leanh::LeanObject,
    mut v___y_3060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3061_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg(v_constName_3057_, v___y_3058_, v___y_3059_);
    leanh::lean_dec(v___y_3059_);
    leanh::lean_dec_ref(v___y_3058_);
    return v_res_3061_;
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0(
    mut v_constName_3062_: *mut leanh::LeanObject,
    mut v___y_3063_: *mut leanh::LeanObject,
    mut v___y_3064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3074_: u8 = 0;
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3066_ = lean_st_ref_get(v___y_3064_);
                v_env_3067_ = leanh::lean_ctor_get(v___x_3066_, 0);
                leanh::lean_inc_ref(v_env_3067_);
                leanh::lean_dec(v___x_3066_);
                v___x_3068_ = 0;
                leanh::lean_inc(v_constName_3062_);
                v___x_3069_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_3067_,
                    v_constName_3062_,
                    v___x_3068_,
                );
                if leanh::lean_obj_tag(v___x_3069_) == 0 {
                    v___x_3070_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg(v_constName_3062_, v___y_3063_, v___y_3064_);
                    return v___x_3070_;
                } else {
                    leanh::lean_dec(v_constName_3062_);
                    v_val_3071_ = leanh::lean_ctor_get(v___x_3069_, 0);
                    v_isSharedCheck_3078_ = (!leanh::lean_is_exclusive(v___x_3069_)) as u8;
                    if v_isSharedCheck_3078_ == 0 {
                        v___x_3073_ = v___x_3069_;
                        v_isShared_3074_ = v_isSharedCheck_3078_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3071_);
                        leanh::lean_dec(v___x_3069_);
                        v___x_3073_ = leanh::lean_box(0);
                        v_isShared_3074_ = v_isSharedCheck_3078_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3074_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3073_, 0);
                    v___x_3076_ = v___x_3073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3077_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_val_3071_);
                    v___x_3076_ = v_reuseFailAlloc_3077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0___boxed(
    mut v_constName_3079_: *mut leanh::LeanObject,
    mut v___y_3080_: *mut leanh::LeanObject,
    mut v___y_3081_: *mut leanh::LeanObject,
    mut v___y_3082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3083_ = l_Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0(v_constName_3079_, v___y_3080_, v___y_3081_);
    leanh::lean_dec(v___y_3081_);
    leanh::lean_dec_ref(v___y_3080_);
    return v_res_3083_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10_spec__14___redArg(
    mut v_x_3084_: *mut leanh::LeanObject,
    mut v_x_3085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3091_: u8 = 0;
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u64 = 0;
    let mut v___x_3094_: u64 = 0;
    let mut v___x_3095_: u64 = 0;
    let mut v_fold_3096_: u64 = 0;
    let mut v___x_3097_: u64 = 0;
    let mut v___x_3098_: u64 = 0;
    let mut v___x_3099_: u64 = 0;
    let mut v___x_3100_: usize = 0;
    let mut v___x_3101_: usize = 0;
    let mut v___x_3102_: usize = 0;
    let mut v___x_3103_: usize = 0;
    let mut v___x_3104_: usize = 0;
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3085_) == 0 {
                    return v_x_3084_;
                } else {
                    v_key_3086_ = leanh::lean_ctor_get(v_x_3085_, 0);
                    v_value_3087_ = leanh::lean_ctor_get(v_x_3085_, 1);
                    v_tail_3088_ = leanh::lean_ctor_get(v_x_3085_, 2);
                    v_isSharedCheck_3111_ = (!leanh::lean_is_exclusive(v_x_3085_)) as u8;
                    if v_isSharedCheck_3111_ == 0 {
                        v___x_3090_ = v_x_3085_;
                        v_isShared_3091_ = v_isSharedCheck_3111_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3088_);
                        leanh::lean_inc(v_value_3087_);
                        leanh::lean_inc(v_key_3086_);
                        leanh::lean_dec(v_x_3085_);
                        v___x_3090_ = leanh::lean_box(0);
                        v_isShared_3091_ = v_isSharedCheck_3111_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3092_ = lean_array_get_size(v_x_3084_);
                v___x_3093_ = l_Lean_Level_hash(v_key_3086_);
                v___x_3094_ = 32u64;
                v___x_3095_ = lean_uint64_shift_right(v___x_3093_, v___x_3094_);
                v_fold_3096_ = lean_uint64_xor(v___x_3093_, v___x_3095_);
                v___x_3097_ = 16u64;
                v___x_3098_ = lean_uint64_shift_right(v_fold_3096_, v___x_3097_);
                v___x_3099_ = lean_uint64_xor(v_fold_3096_, v___x_3098_);
                v___x_3100_ = lean_uint64_to_usize(v___x_3099_);
                v___x_3101_ = lean_usize_of_nat(v___x_3092_);
                v___x_3102_ = 1usize;
                v___x_3103_ = lean_usize_sub(v___x_3101_, v___x_3102_);
                v___x_3104_ = lean_usize_land(v___x_3100_, v___x_3103_);
                v___x_3105_ = lean_array_uget_borrowed(v_x_3084_, v___x_3104_);
                leanh::lean_inc(v___x_3105_);
                if v_isShared_3091_ == 0 {
                    leanh::lean_ctor_set(v___x_3090_, 2, v___x_3105_);
                    v___x_3107_ = v___x_3090_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_key_3086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_value_3087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 2, v___x_3105_);
                    v___x_3107_ = v_reuseFailAlloc_3110_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3108_ = lean_array_uset(v_x_3084_, v___x_3104_, v___x_3107_);
                v_x_3084_ = v___x_3108_;
                v_x_3085_ = v_tail_3088_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10___redArg(
    mut v_i_3112_: *mut leanh::LeanObject,
    mut v_source_3113_: *mut leanh::LeanObject,
    mut v_target_3114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: u8 = 0;
    let mut v_es_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3115_ = lean_array_get_size(v_source_3113_);
                v___x_3116_ = lean_nat_dec_lt(v_i_3112_, v___x_3115_);
                if v___x_3116_ == 0 {
                    leanh::lean_dec_ref(v_source_3113_);
                    leanh::lean_dec(v_i_3112_);
                    return v_target_3114_;
                } else {
                    v_es_3117_ = lean_array_fget(v_source_3113_, v_i_3112_);
                    v___x_3118_ = leanh::lean_box(0);
                    v_source_3119_ = lean_array_fset(v_source_3113_, v_i_3112_, v___x_3118_);
                    v_target_3120_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10_spec__14___redArg(v_target_3114_, v_es_3117_);
                    v___x_3121_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3122_ = lean_nat_add(v_i_3112_, v___x_3121_);
                    leanh::lean_dec(v_i_3112_);
                    v_i_3112_ = v___x_3122_;
                    v_source_3113_ = v_source_3119_;
                    v_target_3114_ = v_target_3120_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6___redArg(
    mut v_data_3124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3125_ = lean_array_get_size(v_data_3124_);
    v___x_3126_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3127_ = lean_nat_mul(v___x_3125_, v___x_3126_);
    v___x_3128_ = leanh::lean_unsigned_to_nat(0);
    v___x_3129_ = leanh::lean_box(0);
    v___x_3130_ = lean_mk_array(v_nbuckets_3127_, v___x_3129_);
    v___x_3131_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10___redArg(v___x_3128_, v_data_3124_, v___x_3130_);
    return v___x_3131_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___redArg(
    mut v_a_3132_: *mut leanh::LeanObject,
    mut v_x_3133_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3134_: u8 = 0;
    let mut v_key_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3133_) == 0 {
                    v___x_3134_ = 0;
                    return v___x_3134_;
                } else {
                    v_key_3135_ = leanh::lean_ctor_get(v_x_3133_, 0);
                    v_tail_3136_ = leanh::lean_ctor_get(v_x_3133_, 2);
                    v___x_3137_ = lean_level_eq(v_key_3135_, v_a_3132_);
                    if v___x_3137_ == 0 {
                        v_x_3133_ = v_tail_3136_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3137_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_a_3139_: *mut leanh::LeanObject,
    mut v_x_3140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3141_: u8 = 0;
    let mut v_r_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3141_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___redArg(v_a_3139_, v_x_3140_);
    leanh::lean_dec(v_x_3140_);
    leanh::lean_dec(v_a_3139_);
    v_r_3142_ = leanh::lean_box((v_res_3141_) as usize);
    return v_r_3142_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3___redArg(
    mut v_m_3143_: *mut leanh::LeanObject,
    mut v_a_3144_: *mut leanh::LeanObject,
    mut v_b_3145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: u64 = 0;
    let mut v___x_3150_: u64 = 0;
    let mut v___x_3151_: u64 = 0;
    let mut v_fold_3152_: u64 = 0;
    let mut v___x_3153_: u64 = 0;
    let mut v___x_3154_: u64 = 0;
    let mut v___x_3155_: u64 = 0;
    let mut v___x_3156_: usize = 0;
    let mut v___x_3157_: usize = 0;
    let mut v___x_3158_: usize = 0;
    let mut v___x_3159_: usize = 0;
    let mut v___x_3160_: usize = 0;
    let mut v_bkt_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: u8 = 0;
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3165_: u8 = 0;
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v_val_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_unused_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3146_ = leanh::lean_ctor_get(v_m_3143_, 0);
                v_buckets_3147_ = leanh::lean_ctor_get(v_m_3143_, 1);
                v___x_3148_ = lean_array_get_size(v_buckets_3147_);
                v___x_3149_ = l_Lean_Level_hash(v_a_3144_);
                v___x_3150_ = 32u64;
                v___x_3151_ = lean_uint64_shift_right(v___x_3149_, v___x_3150_);
                v_fold_3152_ = lean_uint64_xor(v___x_3149_, v___x_3151_);
                v___x_3153_ = 16u64;
                v___x_3154_ = lean_uint64_shift_right(v_fold_3152_, v___x_3153_);
                v___x_3155_ = lean_uint64_xor(v_fold_3152_, v___x_3154_);
                v___x_3156_ = lean_uint64_to_usize(v___x_3155_);
                v___x_3157_ = lean_usize_of_nat(v___x_3148_);
                v___x_3158_ = 1usize;
                v___x_3159_ = lean_usize_sub(v___x_3157_, v___x_3158_);
                v___x_3160_ = lean_usize_land(v___x_3156_, v___x_3159_);
                v_bkt_3161_ = lean_array_uget_borrowed(v_buckets_3147_, v___x_3160_);
                v___x_3162_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___redArg(v_a_3144_, v_bkt_3161_);
                if v___x_3162_ == 0 {
                    leanh::lean_inc_ref(v_buckets_3147_);
                    leanh::lean_inc(v_size_3146_);
                    v_isSharedCheck_3183_ = (!leanh::lean_is_exclusive(v_m_3143_)) as u8;
                    if v_isSharedCheck_3183_ == 0 {
                        v_unused_3184_ = leanh::lean_ctor_get(v_m_3143_, 1);
                        leanh::lean_dec(v_unused_3184_);
                        v_unused_3185_ = leanh::lean_ctor_get(v_m_3143_, 0);
                        leanh::lean_dec(v_unused_3185_);
                        v___x_3164_ = v_m_3143_;
                        v_isShared_3165_ = v_isSharedCheck_3183_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3143_);
                        v___x_3164_ = leanh::lean_box(0);
                        v_isShared_3165_ = v_isSharedCheck_3183_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_3145_);
                    leanh::lean_dec(v_a_3144_);
                    return v_m_3143_;
                }
            }
            1 => {
                v___x_3166_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3167_ = lean_nat_add(v_size_3146_, v___x_3166_);
                leanh::lean_dec(v_size_3146_);
                leanh::lean_inc(v_bkt_3161_);
                v___x_3168_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3168_, 0, v_a_3144_);
                leanh::lean_ctor_set(v___x_3168_, 1, v_b_3145_);
                leanh::lean_ctor_set(v___x_3168_, 2, v_bkt_3161_);
                v_buckets_x27_3169_ = lean_array_uset(v_buckets_3147_, v___x_3160_, v___x_3168_);
                v___x_3170_ = leanh::lean_unsigned_to_nat(4);
                v___x_3171_ = lean_nat_mul(v_size_x27_3167_, v___x_3170_);
                v___x_3172_ = leanh::lean_unsigned_to_nat(3);
                v___x_3173_ = lean_nat_div(v___x_3171_, v___x_3172_);
                leanh::lean_dec(v___x_3171_);
                v___x_3174_ = lean_array_get_size(v_buckets_x27_3169_);
                v___x_3175_ = lean_nat_dec_le(v___x_3173_, v___x_3174_);
                leanh::lean_dec(v___x_3173_);
                if v___x_3175_ == 0 {
                    v_val_3176_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6___redArg(v_buckets_x27_3169_);
                    if v_isShared_3165_ == 0 {
                        leanh::lean_ctor_set(v___x_3164_, 1, v_val_3176_);
                        leanh::lean_ctor_set(v___x_3164_, 0, v_size_x27_3167_);
                        v___x_3178_ = v___x_3164_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3179_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_size_x27_3167_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_val_3176_);
                        v___x_3178_ = v_reuseFailAlloc_3179_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_3165_ == 0 {
                        leanh::lean_ctor_set(v___x_3164_, 1, v_buckets_x27_3169_);
                        leanh::lean_ctor_set(v___x_3164_, 0, v_size_x27_3167_);
                        v___x_3181_ = v___x_3164_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3182_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_size_x27_3167_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_buckets_x27_3169_);
                        v___x_3181_ = v_reuseFailAlloc_3182_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3178_;
            }
            3 => {
                return v___x_3181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg(
    mut v_as_x27_3186_: *mut leanh::LeanObject,
    mut v_b_3187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3186_) == 0 {
                    return v_b_3187_;
                } else {
                    v_head_3188_ = leanh::lean_ctor_get(v_as_x27_3186_, 0);
                    v_tail_3189_ = leanh::lean_ctor_get(v_as_x27_3186_, 1);
                    v___x_3190_ = leanh::lean_box(0);
                    leanh::lean_inc(v_head_3188_);
                    v_r_3191_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3___redArg(v_b_3187_, v_head_3188_, v___x_3190_);
                    v_as_x27_3186_ = v_tail_3189_;
                    v_b_3187_ = v_r_3191_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg___boxed(
    mut v_as_x27_3193_: *mut leanh::LeanObject,
    mut v_b_3194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3195_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg(v_as_x27_3193_, v_b_3194_);
    leanh::lean_dec(v_as_x27_3193_);
    return v_res_3195_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2(
    mut v_m_3196_: *mut leanh::LeanObject,
    mut v_l_3197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3198_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg(v_l_3197_, v_m_3196_);
    return v___x_3198_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2___boxed(
    mut v_m_3199_: *mut leanh::LeanObject,
    mut v_l_3200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2(v_m_3199_, v_l_3200_);
    leanh::lean_dec(v_l_3200_);
    return v_res_3201_;
}
pub unsafe fn _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3205_ = leanh::lean_box(0);
    v___x_3206_ = leanh::lean_unsigned_to_nat(16);
    v___x_3207_ = lean_mk_array(v___x_3206_, v___x_3205_);
    return v___x_3207_;
}
pub unsafe fn _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3208_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2_once), _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2);
    v___x_3209_ = leanh::lean_unsigned_to_nat(0);
    v___x_3210_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3210_, 0, v___x_3209_);
    leanh::lean_ctor_set(v___x_3210_, 1, v___x_3208_);
    return v___x_3210_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(
    mut v_declName_3211_: *mut leanh::LeanObject,
    mut v_a_3212_: *mut leanh::LeanObject,
    mut v_a_3213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3222_: u8 = 0;
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3231_: u8 = 0;
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3243_: u8 = 0;
    let mut v___x_3244_: u8 = 0;
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: u8 = 0;
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3257_: usize = 0;
    let mut v___x_3258_: usize = 0;
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_unused_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3266_: u8 = 0;
    let mut v_a_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3274_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_3211_);
                v___x_3218_ = l_Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0(v_declName_3211_, v_a_3212_, v_a_3213_);
                if leanh::lean_obj_tag(v___x_3218_) == 0 {
                    v_a_3219_ = leanh::lean_ctor_get(v___x_3218_, 0);
                    v_isSharedCheck_3266_ = (!leanh::lean_is_exclusive(v___x_3218_)) as u8;
                    if v_isSharedCheck_3266_ == 0 {
                        v___x_3221_ = v___x_3218_;
                        v_isShared_3222_ = v_isSharedCheck_3266_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3219_);
                        leanh::lean_dec(v___x_3218_);
                        v___x_3221_ = leanh::lean_box(0);
                        v_isShared_3222_ = v_isSharedCheck_3266_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_3211_);
                    v_a_3267_ = leanh::lean_ctor_get(v___x_3218_, 0);
                    v_isSharedCheck_3274_ = (!leanh::lean_is_exclusive(v___x_3218_)) as u8;
                    if v_isSharedCheck_3274_ == 0 {
                        v___x_3269_ = v___x_3218_;
                        v_isShared_3270_ = v_isSharedCheck_3274_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3267_);
                        leanh::lean_dec(v___x_3218_);
                        v___x_3269_ = leanh::lean_box(0);
                        v_isShared_3270_ = v_isSharedCheck_3274_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3216_ = leanh::lean_box(0);
                v___x_3217_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3217_, 0, v___x_3216_);
                return v___x_3217_;
            }
            2 => {
                v_type_3228_ = leanh::lean_ctor_get(v_a_3219_, 2);
                v_isSharedCheck_3263_ = (!leanh::lean_is_exclusive(v_a_3219_)) as u8;
                if v_isSharedCheck_3263_ == 0 {
                    v_unused_3264_ = leanh::lean_ctor_get(v_a_3219_, 1);
                    leanh::lean_dec(v_unused_3264_);
                    v_unused_3265_ = leanh::lean_ctor_get(v_a_3219_, 0);
                    leanh::lean_dec(v_unused_3265_);
                    v___x_3230_ = v_a_3219_;
                    v_isShared_3231_ = v_isSharedCheck_3263_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_type_3228_);
                    leanh::lean_dec(v_a_3219_);
                    v___x_3230_ = leanh::lean_box(0);
                    v_isShared_3231_ = v_isSharedCheck_3263_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_3224_ = leanh::lean_box(0);
                if v_isShared_3222_ == 0 {
                    leanh::lean_ctor_set(v___x_3221_, 0, v___x_3224_);
                    v___x_3226_ = v___x_3221_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3227_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
                    v___x_3226_ = v_reuseFailAlloc_3227_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3226_;
            }
            5 => {
                v___x_3232_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1;
                v___x_3233_ = leanh::lean_unsigned_to_nat(3);
                v___x_3234_ = l_Lean_Expr_isAppOfArity(v_type_3228_, v___x_3232_, v___x_3233_);
                if v___x_3234_ == 0 {
                    leanh::lean_del_object(v___x_3230_);
                    leanh::lean_dec_ref(v_type_3228_);
                    leanh::lean_del_object(v___x_3221_);
                    leanh::lean_dec(v_declName_3211_);
                    state = 1;
                    continue;
                } else {
                    v___x_3235_ = l_Lean_Expr_appFn_x21(v_type_3228_);
                    v___x_3236_ = l_Lean_Expr_appArg_x21(v___x_3235_);
                    leanh::lean_dec_ref(v___x_3235_);
                    if leanh::lean_obj_tag(v___x_3236_) == 4 {
                        v_declName_3237_ = leanh::lean_ctor_get(v___x_3236_, 0);
                        leanh::lean_inc(v_declName_3237_);
                        v_us_3238_ = leanh::lean_ctor_get(v___x_3236_, 1);
                        leanh::lean_inc(v_us_3238_);
                        leanh::lean_dec_ref_known(v___x_3236_, 2);
                        v___x_3239_ = l_Lean_Expr_appArg_x21(v_type_3228_);
                        leanh::lean_dec_ref(v_type_3228_);
                        if leanh::lean_obj_tag(v___x_3239_) == 4 {
                            v_declName_3240_ = leanh::lean_ctor_get(v___x_3239_, 0);
                            leanh::lean_inc(v_declName_3240_);
                            v_us_3241_ = leanh::lean_ctor_get(v___x_3239_, 1);
                            leanh::lean_inc(v_us_3241_);
                            leanh::lean_dec_ref_known(v___x_3239_, 2);
                            v___x_3250_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3_once), _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3);
                            v___x_3251_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg(v_us_3238_, v___x_3250_);
                            v_size_3252_ = leanh::lean_ctor_get(v___x_3251_, 0);
                            leanh::lean_inc(v_size_3252_);
                            v_buckets_3253_ = leanh::lean_ctor_get(v___x_3251_, 1);
                            leanh::lean_inc_ref(v_buckets_3253_);
                            leanh::lean_dec_ref(v___x_3251_);
                            v___x_3254_ = l_List_lengthTR___redArg(v_us_3238_);
                            v___x_3255_ = lean_nat_dec_eq(v_size_3252_, v___x_3254_);
                            leanh::lean_dec(v___x_3254_);
                            leanh::lean_dec(v_size_3252_);
                            if v___x_3255_ == 0 {
                                leanh::lean_dec_ref(v_buckets_3253_);
                                v___y_3243_ = v___x_3255_;
                                state = 6;
                                continue;
                            } else {
                                v___x_3256_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___closed__0;
                                v_sz_3257_ = lean_array_size(v_buckets_3253_);
                                v___x_3258_ = 0usize;
                                v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__4(v_buckets_3253_, v_sz_3257_, v___x_3258_, v___x_3256_);
                                leanh::lean_dec_ref(v_buckets_3253_);
                                v_fst_3260_ = leanh::lean_ctor_get(v___x_3259_, 0);
                                leanh::lean_inc(v_fst_3260_);
                                leanh::lean_dec_ref(v___x_3259_);
                                if leanh::lean_obj_tag(v_fst_3260_) == 0 {
                                    v___y_3243_ = v___x_3255_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_val_3261_ = leanh::lean_ctor_get(v_fst_3260_, 0);
                                    leanh::lean_inc(v_val_3261_);
                                    leanh::lean_dec_ref_known(v_fst_3260_, 1);
                                    v___x_3262_ = (leanh::lean_unbox(v_val_3261_) as u8);
                                    leanh::lean_dec(v_val_3261_);
                                    v___y_3243_ = v___x_3262_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_3239_);
                            leanh::lean_dec(v_us_3238_);
                            leanh::lean_dec(v_declName_3237_);
                            leanh::lean_del_object(v___x_3230_);
                            leanh::lean_del_object(v___x_3221_);
                            leanh::lean_dec(v_declName_3211_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3236_);
                        leanh::lean_del_object(v___x_3230_);
                        leanh::lean_dec_ref(v_type_3228_);
                        leanh::lean_del_object(v___x_3221_);
                        leanh::lean_dec(v_declName_3211_);
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                if v___y_3243_ == 0 {
                    leanh::lean_dec(v_us_3241_);
                    leanh::lean_dec(v_declName_3240_);
                    leanh::lean_dec(v_us_3238_);
                    leanh::lean_dec(v_declName_3237_);
                    leanh::lean_del_object(v___x_3230_);
                    leanh::lean_dec(v_declName_3211_);
                    state = 3;
                    continue;
                } else {
                    v___x_3244_ = l_List_beq___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__1(v_us_3238_, v_us_3241_);
                    leanh::lean_dec(v_us_3241_);
                    leanh::lean_dec(v_us_3238_);
                    if v___x_3244_ == 0 {
                        leanh::lean_dec(v_declName_3240_);
                        leanh::lean_dec(v_declName_3237_);
                        leanh::lean_del_object(v___x_3230_);
                        leanh::lean_dec(v_declName_3211_);
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_3221_);
                        if v_isShared_3231_ == 0 {
                            leanh::lean_ctor_set(v___x_3230_, 2, v_declName_3211_);
                            leanh::lean_ctor_set(v___x_3230_, 1, v_declName_3240_);
                            leanh::lean_ctor_set(v___x_3230_, 0, v_declName_3237_);
                            v___x_3246_ = v___x_3230_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3249_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3249_,
                                0,
                                v_declName_3237_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3249_,
                                1,
                                v_declName_3240_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3249_,
                                2,
                                v_declName_3211_,
                            );
                            v___x_3246_ = v_reuseFailAlloc_3249_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_3247_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3247_, 0, v___x_3246_);
                v___x_3248_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3248_, 0, v___x_3247_);
                return v___x_3248_;
            }
            8 => {
                if v_isShared_3270_ == 0 {
                    v___x_3272_ = v___x_3269_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3273_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
                    v___x_3272_ = v_reuseFailAlloc_3273_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3272_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___boxed(
    mut v_declName_3275_: *mut leanh::LeanObject,
    mut v_a_3276_: *mut leanh::LeanObject,
    mut v_a_3277_: *mut leanh::LeanObject,
    mut v_a_3278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3279_ =
        l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(
            v_declName_3275_,
            v_a_3276_,
            v_a_3277_,
        );
    leanh::lean_dec(v_a_3277_);
    leanh::lean_dec_ref(v_a_3276_);
    return v_res_3279_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0(
    mut v_00_u03b1_3280_: *mut leanh::LeanObject,
    mut v_constName_3281_: *mut leanh::LeanObject,
    mut v___y_3282_: *mut leanh::LeanObject,
    mut v___y_3283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3285_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg(v_constName_3281_, v___y_3282_, v___y_3283_);
    return v___x_3285_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_3286_: *mut leanh::LeanObject,
    mut v_constName_3287_: *mut leanh::LeanObject,
    mut v___y_3288_: *mut leanh::LeanObject,
    mut v___y_3289_: *mut leanh::LeanObject,
    mut v___y_3290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3291_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0(v_00_u03b1_3286_, v_constName_3287_, v___y_3288_, v___y_3289_);
    leanh::lean_dec(v___y_3289_);
    leanh::lean_dec_ref(v___y_3288_);
    return v_res_3291_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3(
    mut v_00_u03b2_3292_: *mut leanh::LeanObject,
    mut v_m_3293_: *mut leanh::LeanObject,
    mut v_a_3294_: *mut leanh::LeanObject,
    mut v_b_3295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3296_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3___redArg(v_m_3293_, v_a_3294_, v_b_3295_);
    return v___x_3296_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4(
    mut v_as_3297_: *mut leanh::LeanObject,
    mut v_as_x27_3298_: *mut leanh::LeanObject,
    mut v_b_3299_: *mut leanh::LeanObject,
    mut v_a_3300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg(v_as_x27_3298_, v_b_3299_);
    return v___x_3301_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___boxed(
    mut v_as_3302_: *mut leanh::LeanObject,
    mut v_as_x27_3303_: *mut leanh::LeanObject,
    mut v_b_3304_: *mut leanh::LeanObject,
    mut v_a_3305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3306_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4(v_as_3302_, v_as_x27_3303_, v_b_3304_, v_a_3305_);
    leanh::lean_dec(v_as_x27_3303_);
    leanh::lean_dec(v_as_3302_);
    return v_res_3306_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3307_: *mut leanh::LeanObject,
    mut v_ref_3308_: *mut leanh::LeanObject,
    mut v_constName_3309_: *mut leanh::LeanObject,
    mut v___y_3310_: *mut leanh::LeanObject,
    mut v___y_3311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3313_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg(v_ref_3308_, v_constName_3309_, v___y_3310_, v___y_3311_);
    return v___x_3313_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3314_: *mut leanh::LeanObject,
    mut v_ref_3315_: *mut leanh::LeanObject,
    mut v_constName_3316_: *mut leanh::LeanObject,
    mut v___y_3317_: *mut leanh::LeanObject,
    mut v___y_3318_: *mut leanh::LeanObject,
    mut v___y_3319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1(v_00_u03b1_3314_, v_ref_3315_, v_constName_3316_, v___y_3317_, v___y_3318_);
    leanh::lean_dec(v___y_3318_);
    leanh::lean_dec_ref(v___y_3317_);
    leanh::lean_dec(v_ref_3315_);
    return v_res_3320_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5(
    mut v_00_u03b2_3321_: *mut leanh::LeanObject,
    mut v_a_3322_: *mut leanh::LeanObject,
    mut v_x_3323_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3324_: u8 = 0;
    v___x_3324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___redArg(v_a_3322_, v_x_3323_);
    return v___x_3324_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b2_3325_: *mut leanh::LeanObject,
    mut v_a_3326_: *mut leanh::LeanObject,
    mut v_x_3327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3328_: u8 = 0;
    let mut v_r_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5(v_00_u03b2_3325_, v_a_3326_, v_x_3327_);
    leanh::lean_dec(v_x_3327_);
    leanh::lean_dec(v_a_3326_);
    v_r_3329_ = leanh::lean_box((v_res_3328_) as usize);
    return v_r_3329_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6(
    mut v_00_u03b2_3330_: *mut leanh::LeanObject,
    mut v_data_3331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3332_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6___redArg(v_data_3331_);
    return v___x_3332_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6(
    mut v_00_u03b1_3333_: *mut leanh::LeanObject,
    mut v_ref_3334_: *mut leanh::LeanObject,
    mut v_msg_3335_: *mut leanh::LeanObject,
    mut v_declHint_3336_: *mut leanh::LeanObject,
    mut v___y_3337_: *mut leanh::LeanObject,
    mut v___y_3338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3340_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_3334_, v_msg_3335_, v_declHint_3336_, v___y_3337_, v___y_3338_);
    return v___x_3340_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___boxed(
    mut v_00_u03b1_3341_: *mut leanh::LeanObject,
    mut v_ref_3342_: *mut leanh::LeanObject,
    mut v_msg_3343_: *mut leanh::LeanObject,
    mut v_declHint_3344_: *mut leanh::LeanObject,
    mut v___y_3345_: *mut leanh::LeanObject,
    mut v___y_3346_: *mut leanh::LeanObject,
    mut v___y_3347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3348_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_3341_, v_ref_3342_, v_msg_3343_, v_declHint_3344_, v___y_3345_, v___y_3346_);
    leanh::lean_dec(v___y_3346_);
    leanh::lean_dec_ref(v___y_3345_);
    leanh::lean_dec(v_ref_3342_);
    return v_res_3348_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10(
    mut v_00_u03b2_3349_: *mut leanh::LeanObject,
    mut v_i_3350_: *mut leanh::LeanObject,
    mut v_source_3351_: *mut leanh::LeanObject,
    mut v_target_3352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3353_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10___redArg(v_i_3350_, v_source_3351_, v_target_3352_);
    return v___x_3353_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12(
    mut v_msg_3354_: *mut leanh::LeanObject,
    mut v_declHint_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
    mut v___y_3357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3359_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg(v_msg_3354_, v_declHint_3355_, v___y_3357_);
    return v___x_3359_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___boxed(
    mut v_msg_3360_: *mut leanh::LeanObject,
    mut v_declHint_3361_: *mut leanh::LeanObject,
    mut v___y_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
    mut v___y_3364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3365_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12(v_msg_3360_, v_declHint_3361_, v___y_3362_, v___y_3363_);
    leanh::lean_dec(v___y_3363_);
    leanh::lean_dec_ref(v___y_3362_);
    return v_res_3365_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10(
    mut v_00_u03b1_3366_: *mut leanh::LeanObject,
    mut v_ref_3367_: *mut leanh::LeanObject,
    mut v_msg_3368_: *mut leanh::LeanObject,
    mut v___y_3369_: *mut leanh::LeanObject,
    mut v___y_3370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3372_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_ref_3367_, v_msg_3368_, v___y_3369_, v___y_3370_);
    return v___x_3372_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___boxed(
    mut v_00_u03b1_3373_: *mut leanh::LeanObject,
    mut v_ref_3374_: *mut leanh::LeanObject,
    mut v_msg_3375_: *mut leanh::LeanObject,
    mut v___y_3376_: *mut leanh::LeanObject,
    mut v___y_3377_: *mut leanh::LeanObject,
    mut v___y_3378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3379_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10(v_00_u03b1_3373_, v_ref_3374_, v_msg_3375_, v___y_3376_, v___y_3377_);
    leanh::lean_dec(v___y_3377_);
    leanh::lean_dec_ref(v___y_3376_);
    leanh::lean_dec(v_ref_3374_);
    return v_res_3379_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10_spec__14(
    mut v_00_u03b2_3380_: *mut leanh::LeanObject,
    mut v_x_3381_: *mut leanh::LeanObject,
    mut v_x_3382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3383_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10_spec__14___redArg(v_x_3381_, v_x_3382_);
    return v___x_3383_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14(
    mut v_00_u03b1_3384_: *mut leanh::LeanObject,
    mut v_msg_3385_: *mut leanh::LeanObject,
    mut v___y_3386_: *mut leanh::LeanObject,
    mut v___y_3387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3389_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(v_msg_3385_, v___y_3386_, v___y_3387_);
    return v___x_3389_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___boxed(
    mut v_00_u03b1_3390_: *mut leanh::LeanObject,
    mut v_msg_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
    mut v___y_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3395_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14(v_00_u03b1_3390_, v_msg_3391_, v___y_3392_, v___y_3393_);
    leanh::lean_dec(v___y_3393_);
    leanh::lean_dec_ref(v___y_3392_);
    return v_res_3395_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3396_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3396_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3397_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0);
    v___x_3398_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3398_, 0, v___x_3397_);
    return v___x_3398_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1);
    v___x_3400_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3400_, 0, v___x_3399_);
    leanh::lean_ctor_set(v___x_3400_, 1, v___x_3399_);
    return v___x_3400_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg(
    mut v_ext_3401_: *mut leanh::LeanObject,
    mut v_b_3402_: *mut leanh::LeanObject,
    mut v_kind_3403_: u8,
    mut v___y_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_currNamespace_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3419_: u8 = 0;
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3428_: u8 = 0;
    let mut v_unused_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_3407_ = leanh::lean_ctor_get(v___y_3404_, 6);
                v___x_3408_ = lean_st_ref_take(v___y_3405_);
                v_env_3409_ = leanh::lean_ctor_get(v___x_3408_, 0);
                v_nextMacroScope_3410_ = leanh::lean_ctor_get(v___x_3408_, 1);
                v_ngen_3411_ = leanh::lean_ctor_get(v___x_3408_, 2);
                v_auxDeclNGen_3412_ = leanh::lean_ctor_get(v___x_3408_, 3);
                v_traceState_3413_ = leanh::lean_ctor_get(v___x_3408_, 4);
                v_messages_3414_ = leanh::lean_ctor_get(v___x_3408_, 6);
                v_infoState_3415_ = leanh::lean_ctor_get(v___x_3408_, 7);
                v_snapshotTasks_3416_ = leanh::lean_ctor_get(v___x_3408_, 8);
                v_isSharedCheck_3428_ = (!leanh::lean_is_exclusive(v___x_3408_)) as u8;
                if v_isSharedCheck_3428_ == 0 {
                    v_unused_3429_ = leanh::lean_ctor_get(v___x_3408_, 5);
                    leanh::lean_dec(v_unused_3429_);
                    v___x_3418_ = v___x_3408_;
                    v_isShared_3419_ = v_isSharedCheck_3428_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3416_);
                    leanh::lean_inc(v_infoState_3415_);
                    leanh::lean_inc(v_messages_3414_);
                    leanh::lean_inc(v_traceState_3413_);
                    leanh::lean_inc(v_auxDeclNGen_3412_);
                    leanh::lean_inc(v_ngen_3411_);
                    leanh::lean_inc(v_nextMacroScope_3410_);
                    leanh::lean_inc(v_env_3409_);
                    leanh::lean_dec(v___x_3408_);
                    v___x_3418_ = leanh::lean_box(0);
                    v_isShared_3419_ = v_isSharedCheck_3428_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_currNamespace_3407_);
                v___x_3420_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_3409_,
                    v_ext_3401_,
                    v_b_3402_,
                    v_kind_3403_,
                    v_currNamespace_3407_,
                );
                v___x_3421_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2);
                if v_isShared_3419_ == 0 {
                    leanh::lean_ctor_set(v___x_3418_, 5, v___x_3421_);
                    leanh::lean_ctor_set(v___x_3418_, 0, v___x_3420_);
                    v___x_3423_ = v___x_3418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3427_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_nextMacroScope_3410_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 2, v_ngen_3411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 3, v_auxDeclNGen_3412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 4, v_traceState_3413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 5, v___x_3421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 6, v_messages_3414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 7, v_infoState_3415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 8, v_snapshotTasks_3416_);
                    v___x_3423_ = v_reuseFailAlloc_3427_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3424_ = lean_st_ref_set(v___y_3405_, v___x_3423_);
                v___x_3425_ = leanh::lean_box(0);
                v___x_3426_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3426_, 0, v___x_3425_);
                return v___x_3426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___boxed(
    mut v_ext_3430_: *mut leanh::LeanObject,
    mut v_b_3431_: *mut leanh::LeanObject,
    mut v_kind_3432_: *mut leanh::LeanObject,
    mut v___y_3433_: *mut leanh::LeanObject,
    mut v___y_3434_: *mut leanh::LeanObject,
    mut v___y_3435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_3436_: u8 = 0;
    let mut v_res_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3436_ = (leanh::lean_unbox(v_kind_3432_) as u8);
    v_res_3437_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg(
        v_ext_3430_,
        v_b_3431_,
        v_kind_boxed_3436_,
        v___y_3433_,
        v___y_3434_,
    );
    leanh::lean_dec(v___y_3434_);
    leanh::lean_dec_ref(v___y_3433_);
    return v_res_3437_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0(
    mut v_00_u03b1_3438_: *mut leanh::LeanObject,
    mut v_00_u03b2_3439_: *mut leanh::LeanObject,
    mut v_00_u03c3_3440_: *mut leanh::LeanObject,
    mut v_ext_3441_: *mut leanh::LeanObject,
    mut v_b_3442_: *mut leanh::LeanObject,
    mut v_kind_3443_: u8,
    mut v___y_3444_: *mut leanh::LeanObject,
    mut v___y_3445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3447_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg(
        v_ext_3441_,
        v_b_3442_,
        v_kind_3443_,
        v___y_3444_,
        v___y_3445_,
    );
    return v___x_3447_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___boxed(
    mut v_00_u03b1_3448_: *mut leanh::LeanObject,
    mut v_00_u03b2_3449_: *mut leanh::LeanObject,
    mut v_00_u03c3_3450_: *mut leanh::LeanObject,
    mut v_ext_3451_: *mut leanh::LeanObject,
    mut v_b_3452_: *mut leanh::LeanObject,
    mut v_kind_3453_: *mut leanh::LeanObject,
    mut v___y_3454_: *mut leanh::LeanObject,
    mut v___y_3455_: *mut leanh::LeanObject,
    mut v___y_3456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_3457_: u8 = 0;
    let mut v_res_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3457_ = (leanh::lean_unbox(v_kind_3453_) as u8);
    v_res_3458_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0(
        v_00_u03b1_3448_,
        v_00_u03b2_3449_,
        v_00_u03c3_3450_,
        v_ext_3451_,
        v_b_3452_,
        v_kind_boxed_3457_,
        v___y_3454_,
        v___y_3455_,
    );
    leanh::lean_dec(v___y_3455_);
    leanh::lean_dec_ref(v___y_3454_);
    return v_res_3458_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_add___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3460_ = l_Lean_Compiler_CSimp_add___closed__0;
    v___x_3461_ = l_Lean_stringToMessageData(v___x_3460_);
    return v___x_3461_;
}
pub unsafe fn l_Lean_Compiler_CSimp_add(
    mut v_declName_3462_: *mut leanh::LeanObject,
    mut v_kind_3463_: u8,
    mut v_a_3464_: *mut leanh::LeanObject,
    mut v_a_3465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3477_: u8 = 0;
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3467_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(v_declName_3462_, v_a_3464_, v_a_3465_);
                if leanh::lean_obj_tag(v___x_3467_) == 0 {
                    v_a_3468_ = leanh::lean_ctor_get(v___x_3467_, 0);
                    leanh::lean_inc(v_a_3468_);
                    leanh::lean_dec_ref_known(v___x_3467_, 1);
                    if leanh::lean_obj_tag(v_a_3468_) == 1 {
                        v_val_3469_ = leanh::lean_ctor_get(v_a_3468_, 0);
                        leanh::lean_inc(v_val_3469_);
                        leanh::lean_dec_ref_known(v_a_3468_, 1);
                        v___x_3470_ = l_Lean_Compiler_CSimp_ext;
                        v___x_3471_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg(v___x_3470_, v_val_3469_, v_kind_3463_, v_a_3464_, v_a_3465_);
                        return v___x_3471_;
                    } else {
                        leanh::lean_dec(v_a_3468_);
                        v___x_3472_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_add___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_add___closed__1_once),
                            _init_l_Lean_Compiler_CSimp_add___closed__1,
                        );
                        v___x_3473_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(v___x_3472_, v_a_3464_, v_a_3465_);
                        return v___x_3473_;
                    }
                } else {
                    v_a_3474_ = leanh::lean_ctor_get(v___x_3467_, 0);
                    v_isSharedCheck_3481_ = (!leanh::lean_is_exclusive(v___x_3467_)) as u8;
                    if v_isSharedCheck_3481_ == 0 {
                        v___x_3476_ = v___x_3467_;
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3474_);
                        leanh::lean_dec(v___x_3467_);
                        v___x_3476_ = leanh::lean_box(0);
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3477_ == 0 {
                    v___x_3479_ = v___x_3476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3480_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
                    v___x_3479_ = v_reuseFailAlloc_3480_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_CSimp_add___boxed(
    mut v_declName_3482_: *mut leanh::LeanObject,
    mut v_kind_3483_: *mut leanh::LeanObject,
    mut v_a_3484_: *mut leanh::LeanObject,
    mut v_a_3485_: *mut leanh::LeanObject,
    mut v_a_3486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_3487_: u8 = 0;
    let mut v_res_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3487_ = (leanh::lean_unbox(v_kind_3483_) as u8);
    v_res_3488_ =
        l_Lean_Compiler_CSimp_add(v_declName_3482_, v_kind_boxed_3487_, v_a_3484_, v_a_3485_);
    leanh::lean_dec(v_a_3485_);
    leanh::lean_dec_ref(v_a_3484_);
    return v_res_3488_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0(
    mut v___x_3489_: *mut leanh::LeanObject,
    mut v_declName_3490_: *mut leanh::LeanObject,
    mut v_stx_3491_: *mut leanh::LeanObject,
    mut v_attrKind_3492_: u8,
    mut v___y_3493_: *mut leanh::LeanObject,
    mut v___y_3494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3501_: u8 = 0;
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3506_: u8 = 0;
    let mut v_unused_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3496_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3491_, v___y_3493_, v___y_3494_);
                if leanh::lean_obj_tag(v___x_3496_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3496_, 1);
                    leanh::lean_inc(v_declName_3490_);
                    v___x_3497_ = l_Lean_ensureAttrDeclIsPublic(
                        v___x_3489_,
                        v_declName_3490_,
                        v_attrKind_3492_,
                        v___y_3493_,
                        v___y_3494_,
                    );
                    if leanh::lean_obj_tag(v___x_3497_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3497_, 1);
                        v___x_3498_ = l_Lean_Compiler_CSimp_add(
                            v_declName_3490_,
                            v_attrKind_3492_,
                            v___y_3493_,
                            v___y_3494_,
                        );
                        if leanh::lean_obj_tag(v___x_3498_) == 0 {
                            v_isSharedCheck_3506_ =
                                (!leanh::lean_is_exclusive(v___x_3498_)) as u8;
                            if v_isSharedCheck_3506_ == 0 {
                                v_unused_3507_ = leanh::lean_ctor_get(v___x_3498_, 0);
                                leanh::lean_dec(v_unused_3507_);
                                v___x_3500_ = v___x_3498_;
                                v_isShared_3501_ = v_isSharedCheck_3506_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3498_);
                                v___x_3500_ = leanh::lean_box(0);
                                v_isShared_3501_ = v_isSharedCheck_3506_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_3498_;
                        }
                    } else {
                        leanh::lean_dec(v_declName_3490_);
                        return v___x_3497_;
                    }
                } else {
                    leanh::lean_dec(v_declName_3490_);
                    leanh::lean_dec(v___x_3489_);
                    return v___x_3496_;
                }
            }
            1 => {
                v___x_3502_ = leanh::lean_box(0);
                if v_isShared_3501_ == 0 {
                    leanh::lean_ctor_set(v___x_3500_, 0, v___x_3502_);
                    v___x_3504_ = v___x_3500_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3505_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
                    v___x_3504_ = v_reuseFailAlloc_3505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0___boxed(
    mut v___x_3508_: *mut leanh::LeanObject,
    mut v_declName_3509_: *mut leanh::LeanObject,
    mut v_stx_3510_: *mut leanh::LeanObject,
    mut v_attrKind_3511_: *mut leanh::LeanObject,
    mut v___y_3512_: *mut leanh::LeanObject,
    mut v___y_3513_: *mut leanh::LeanObject,
    mut v___y_3514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_attrKind_boxed_3515_: u8 = 0;
    let mut v_res_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_3515_ = (leanh::lean_unbox(v_attrKind_3511_) as u8);
    v_res_3516_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0(
        v___x_3508_,
        v_declName_3509_,
        v_stx_3510_,
        v_attrKind_boxed_3515_,
        v___y_3512_,
        v___y_3513_,
    );
    leanh::lean_dec(v___y_3513_);
    leanh::lean_dec_ref(v___y_3512_);
    return v_res_3516_;
}
pub unsafe fn _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3518_ =
        l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__0;
    v___x_3519_ = l_Lean_stringToMessageData(v___x_3518_);
    return v___x_3519_;
}
pub unsafe fn _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3521_ =
        l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__2;
    v___x_3522_ = l_Lean_stringToMessageData(v___x_3521_);
    return v___x_3522_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1(
    mut v___x_3523_: *mut leanh::LeanObject,
    mut v_decl_3524_: *mut leanh::LeanObject,
    mut v___y_3525_: *mut leanh::LeanObject,
    mut v___y_3526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3528_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1_once), _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1);
    v___x_3529_ = l_Lean_MessageData_ofName(v___x_3523_);
    v___x_3530_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3530_, 0, v___x_3528_);
    leanh::lean_ctor_set(v___x_3530_, 1, v___x_3529_);
    v___x_3531_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3_once), _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3);
    v___x_3532_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3532_, 0, v___x_3530_);
    leanh::lean_ctor_set(v___x_3532_, 1, v___x_3531_);
    v___x_3533_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(v___x_3532_, v___y_3525_, v___y_3526_);
    return v___x_3533_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___boxed(
    mut v___x_3534_: *mut leanh::LeanObject,
    mut v_decl_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
    mut v___y_3537_: *mut leanh::LeanObject,
    mut v___y_3538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3539_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1(
        v___x_3534_,
        v_decl_3535_,
        v___y_3536_,
        v___y_3537_,
    );
    leanh::lean_dec(v___y_3537_);
    leanh::lean_dec_ref(v___y_3536_);
    leanh::lean_dec(v_decl_3535_);
    return v_res_3539_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn()
-> *mut leanh::LeanObject {
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3588_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__18;
    v___x_3589_ = l_Lean_registerBuiltinAttribute(v___x_3588_);
    return v___x_3589_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___boxed(
    mut v_a_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3591_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn();
    return v_res_3591_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1()
-> *mut leanh::LeanObject {
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3594_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__11;
    v___x_3595_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1___closed__0;
    v___x_3596_ = l_Lean_addBuiltinDocString(v___x_3594_, v___x_3595_);
    return v___x_3596_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1___boxed(
    mut v_a_3597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3598_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1();
    return v_res_3598_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___lam__0(
    mut v___y_3599_: *mut leanh::LeanObject,
    mut v_isExporting_3600_: u8,
    mut v___x_3601_: *mut leanh::LeanObject,
    mut v_a_x3f_3602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3623_: u8 = 0;
    let mut v_unused_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3604_ = lean_st_ref_take(v___y_3599_);
                v_env_3605_ = leanh::lean_ctor_get(v___x_3604_, 0);
                v_nextMacroScope_3606_ = leanh::lean_ctor_get(v___x_3604_, 1);
                v_ngen_3607_ = leanh::lean_ctor_get(v___x_3604_, 2);
                v_auxDeclNGen_3608_ = leanh::lean_ctor_get(v___x_3604_, 3);
                v_traceState_3609_ = leanh::lean_ctor_get(v___x_3604_, 4);
                v_messages_3610_ = leanh::lean_ctor_get(v___x_3604_, 6);
                v_infoState_3611_ = leanh::lean_ctor_get(v___x_3604_, 7);
                v_snapshotTasks_3612_ = leanh::lean_ctor_get(v___x_3604_, 8);
                v_isSharedCheck_3623_ = (!leanh::lean_is_exclusive(v___x_3604_)) as u8;
                if v_isSharedCheck_3623_ == 0 {
                    v_unused_3624_ = leanh::lean_ctor_get(v___x_3604_, 5);
                    leanh::lean_dec(v_unused_3624_);
                    v___x_3614_ = v___x_3604_;
                    v_isShared_3615_ = v_isSharedCheck_3623_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3612_);
                    leanh::lean_inc(v_infoState_3611_);
                    leanh::lean_inc(v_messages_3610_);
                    leanh::lean_inc(v_traceState_3609_);
                    leanh::lean_inc(v_auxDeclNGen_3608_);
                    leanh::lean_inc(v_ngen_3607_);
                    leanh::lean_inc(v_nextMacroScope_3606_);
                    leanh::lean_inc(v_env_3605_);
                    leanh::lean_dec(v___x_3604_);
                    v___x_3614_ = leanh::lean_box(0);
                    v_isShared_3615_ = v_isSharedCheck_3623_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3616_ = l_Lean_Environment_setExporting(v_env_3605_, v_isExporting_3600_);
                if v_isShared_3615_ == 0 {
                    leanh::lean_ctor_set(v___x_3614_, 5, v___x_3601_);
                    leanh::lean_ctor_set(v___x_3614_, 0, v___x_3616_);
                    v___x_3618_ = v___x_3614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3622_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3616_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_nextMacroScope_3606_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 2, v_ngen_3607_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 3, v_auxDeclNGen_3608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 4, v_traceState_3609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 5, v___x_3601_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 6, v_messages_3610_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 7, v_infoState_3611_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 8, v_snapshotTasks_3612_);
                    v___x_3618_ = v_reuseFailAlloc_3622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3619_ = lean_st_ref_set(v___y_3599_, v___x_3618_);
                v___x_3620_ = leanh::lean_box(0);
                v___x_3621_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3621_, 0, v___x_3620_);
                return v___x_3621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___lam__0___boxed(
    mut v___y_3625_: *mut leanh::LeanObject,
    mut v_isExporting_3626_: *mut leanh::LeanObject,
    mut v___x_3627_: *mut leanh::LeanObject,
    mut v_a_x3f_3628_: *mut leanh::LeanObject,
    mut v___y_3629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_3630_: u8 = 0;
    let mut v_res_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3630_ = (leanh::lean_unbox(v_isExporting_3626_) as u8);
    v_res_3631_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___lam__0(v___y_3625_, v_isExporting_boxed_3630_, v___x_3627_, v_a_x3f_3628_);
    leanh::lean_dec(v_a_x3f_3628_);
    leanh::lean_dec(v___y_3625_);
    return v_res_3631_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg(
    mut v_x_3632_: *mut leanh::LeanObject,
    mut v_isExporting_3633_: u8,
    mut v___y_3634_: *mut leanh::LeanObject,
    mut v___y_3635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3639_: u8 = 0;
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3667_: u8 = 0;
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut v_unused_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut v_a_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3680_: u8 = 0;
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3684_: u8 = 0;
    let mut v_unused_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut v_unused_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3637_ = lean_st_ref_get(v___y_3635_);
                v_env_3638_ = leanh::lean_ctor_get(v___x_3637_, 0);
                leanh::lean_inc_ref(v_env_3638_);
                leanh::lean_dec(v___x_3637_);
                v_isExporting_3639_ = leanh::lean_ctor_get_uint8(
                    v_env_3638_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_3638_);
                v___x_3640_ = lean_st_ref_take(v___y_3635_);
                v_env_3641_ = leanh::lean_ctor_get(v___x_3640_, 0);
                v_nextMacroScope_3642_ = leanh::lean_ctor_get(v___x_3640_, 1);
                v_ngen_3643_ = leanh::lean_ctor_get(v___x_3640_, 2);
                v_auxDeclNGen_3644_ = leanh::lean_ctor_get(v___x_3640_, 3);
                v_traceState_3645_ = leanh::lean_ctor_get(v___x_3640_, 4);
                v_messages_3646_ = leanh::lean_ctor_get(v___x_3640_, 6);
                v_infoState_3647_ = leanh::lean_ctor_get(v___x_3640_, 7);
                v_snapshotTasks_3648_ = leanh::lean_ctor_get(v___x_3640_, 8);
                v_isSharedCheck_3687_ = (!leanh::lean_is_exclusive(v___x_3640_)) as u8;
                if v_isSharedCheck_3687_ == 0 {
                    v_unused_3688_ = leanh::lean_ctor_get(v___x_3640_, 5);
                    leanh::lean_dec(v_unused_3688_);
                    v___x_3650_ = v___x_3640_;
                    v_isShared_3651_ = v_isSharedCheck_3687_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3648_);
                    leanh::lean_inc(v_infoState_3647_);
                    leanh::lean_inc(v_messages_3646_);
                    leanh::lean_inc(v_traceState_3645_);
                    leanh::lean_inc(v_auxDeclNGen_3644_);
                    leanh::lean_inc(v_ngen_3643_);
                    leanh::lean_inc(v_nextMacroScope_3642_);
                    leanh::lean_inc(v_env_3641_);
                    leanh::lean_dec(v___x_3640_);
                    v___x_3650_ = leanh::lean_box(0);
                    v_isShared_3651_ = v_isSharedCheck_3687_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3652_ = l_Lean_Environment_setExporting(v_env_3641_, v_isExporting_3633_);
                v___x_3653_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2);
                if v_isShared_3651_ == 0 {
                    leanh::lean_ctor_set(v___x_3650_, 5, v___x_3653_);
                    leanh::lean_ctor_set(v___x_3650_, 0, v___x_3652_);
                    v___x_3655_ = v___x_3650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3686_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3652_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_nextMacroScope_3642_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 2, v_ngen_3643_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 3, v_auxDeclNGen_3644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 4, v_traceState_3645_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 5, v___x_3653_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 6, v_messages_3646_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 7, v_infoState_3647_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 8, v_snapshotTasks_3648_);
                    v___x_3655_ = v_reuseFailAlloc_3686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3656_ = lean_st_ref_set(v___y_3635_, v___x_3655_);
                leanh::lean_inc(v___y_3635_);
                leanh::lean_inc_ref(v___y_3634_);
                v_r_3657_ = leanh::lean_apply_3(
                    v_x_3632_,
                    v___y_3634_,
                    v___y_3635_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_3657_) == 0 {
                    v_a_3658_ = leanh::lean_ctor_get(v_r_3657_, 0);
                    v_isSharedCheck_3674_ = (!leanh::lean_is_exclusive(v_r_3657_)) as u8;
                    if v_isSharedCheck_3674_ == 0 {
                        v___x_3660_ = v_r_3657_;
                        v_isShared_3661_ = v_isSharedCheck_3674_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3658_);
                        leanh::lean_dec(v_r_3657_);
                        v___x_3660_ = leanh::lean_box(0);
                        v_isShared_3661_ = v_isSharedCheck_3674_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_3675_ = leanh::lean_ctor_get(v_r_3657_, 0);
                    leanh::lean_inc(v_a_3675_);
                    leanh::lean_dec_ref_known(v_r_3657_, 1);
                    v___x_3676_ = leanh::lean_box(0);
                    v___x_3677_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___lam__0(v___y_3635_, v_isExporting_3639_, v___x_3653_, v___x_3676_);
                    v_isSharedCheck_3684_ = (!leanh::lean_is_exclusive(v___x_3677_)) as u8;
                    if v_isSharedCheck_3684_ == 0 {
                        v_unused_3685_ = leanh::lean_ctor_get(v___x_3677_, 0);
                        leanh::lean_dec(v_unused_3685_);
                        v___x_3679_ = v___x_3677_;
                        v_isShared_3680_ = v_isSharedCheck_3684_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3677_);
                        v___x_3679_ = leanh::lean_box(0);
                        v_isShared_3680_ = v_isSharedCheck_3684_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_a_3658_);
                if v_isShared_3661_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3660_, 1);
                    v___x_3663_ = v___x_3660_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3658_);
                    v___x_3663_ = v_reuseFailAlloc_3673_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3664_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___lam__0(v___y_3635_, v_isExporting_3639_, v___x_3653_, v___x_3663_);
                leanh::lean_dec_ref(v___x_3663_);
                v_isSharedCheck_3671_ = (!leanh::lean_is_exclusive(v___x_3664_)) as u8;
                if v_isSharedCheck_3671_ == 0 {
                    v_unused_3672_ = leanh::lean_ctor_get(v___x_3664_, 0);
                    leanh::lean_dec(v_unused_3672_);
                    v___x_3666_ = v___x_3664_;
                    v_isShared_3667_ = v_isSharedCheck_3671_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3664_);
                    v___x_3666_ = leanh::lean_box(0);
                    v_isShared_3667_ = v_isSharedCheck_3671_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3667_ == 0 {
                    leanh::lean_ctor_set(v___x_3666_, 0, v_a_3658_);
                    v___x_3669_ = v___x_3666_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3658_);
                    v___x_3669_ = v_reuseFailAlloc_3670_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3669_;
            }
            7 => {
                if v_isShared_3680_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3679_, 1);
                    leanh::lean_ctor_set(v___x_3679_, 0, v_a_3675_);
                    v___x_3682_ = v___x_3679_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3683_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3675_);
                    v___x_3682_ = v_reuseFailAlloc_3683_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3682_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___boxed(
    mut v_x_3689_: *mut leanh::LeanObject,
    mut v_isExporting_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_3694_: u8 = 0;
    let mut v_res_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3694_ = (leanh::lean_unbox(v_isExporting_3690_) as u8);
    v_res_3695_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg(v_x_3689_, v_isExporting_boxed_3694_, v___y_3691_, v___y_3692_);
    leanh::lean_dec(v___y_3692_);
    leanh::lean_dec_ref(v___y_3691_);
    return v_res_3695_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___redArg(
    mut v_x_3696_: *mut leanh::LeanObject,
    mut v_when_3697_: u8,
    mut v___y_3698_: *mut leanh::LeanObject,
    mut v___y_3699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_3697_ == 0 {
        let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_3699_);
        leanh::lean_inc_ref(v___y_3698_);
        v___x_3701_ = leanh::lean_apply_3(
            v_x_3696_,
            v___y_3698_,
            v___y_3699_,
            leanh::lean_box(0),
        );
        return v___x_3701_;
    } else {
        let mut v___x_3702_: u8 = 0;
        let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3702_ = 0;
        v___x_3703_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg(v_x_3696_, v___x_3702_, v___y_3698_, v___y_3699_);
        return v___x_3703_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___redArg___boxed(
    mut v_x_3704_: *mut leanh::LeanObject,
    mut v_when_3705_: *mut leanh::LeanObject,
    mut v___y_3706_: *mut leanh::LeanObject,
    mut v___y_3707_: *mut leanh::LeanObject,
    mut v___y_3708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_3709_: u8 = 0;
    let mut v_res_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_3709_ = (leanh::lean_unbox(v_when_3705_) as u8);
    v_res_3710_ =
        l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___redArg(
            v_x_3704_,
            v_when_boxed_3709_,
            v___y_3706_,
            v___y_3707_,
        );
    leanh::lean_dec(v___y_3707_);
    leanh::lean_dec_ref(v___y_3706_);
    return v_res_3710_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___redArg(
    mut v_a_3711_: *mut leanh::LeanObject,
    mut v_x_3712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: u8 = 0;
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3712_) == 0 {
                    v___x_3713_ = leanh::lean_box(0);
                    return v___x_3713_;
                } else {
                    v_key_3714_ = leanh::lean_ctor_get(v_x_3712_, 0);
                    v_value_3715_ = leanh::lean_ctor_get(v_x_3712_, 1);
                    v_tail_3716_ = leanh::lean_ctor_get(v_x_3712_, 2);
                    v___x_3717_ = lean_name_eq(v_key_3714_, v_a_3711_);
                    if v___x_3717_ == 0 {
                        v_x_3712_ = v_tail_3716_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3715_);
                        v___x_3719_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3719_, 0, v_value_3715_);
                        return v___x_3719_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_3720_: *mut leanh::LeanObject,
    mut v_x_3721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3722_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___redArg(v_a_3720_, v_x_3721_);
    leanh::lean_dec(v_x_3721_);
    leanh::lean_dec(v_a_3720_);
    return v_res_3722_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(
    mut v_m_3723_: *mut leanh::LeanObject,
    mut v_a_3724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3728_: u64 = 0;
    let mut v___x_3729_: u64 = 0;
    let mut v___x_3730_: u64 = 0;
    let mut v_fold_3731_: u64 = 0;
    let mut v___x_3732_: u64 = 0;
    let mut v___x_3733_: u64 = 0;
    let mut v___x_3734_: u64 = 0;
    let mut v___x_3735_: usize = 0;
    let mut v___x_3736_: usize = 0;
    let mut v___x_3737_: usize = 0;
    let mut v___x_3738_: usize = 0;
    let mut v___x_3739_: usize = 0;
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: u64 = 0;
    let mut v_hash_3743_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3725_ = leanh::lean_ctor_get(v_m_3723_, 1);
                v___x_3726_ = lean_array_get_size(v_buckets_3725_);
                if leanh::lean_obj_tag(v_a_3724_) == 0 {
                    v___x_3742_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_3728_ = v___x_3742_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3743_ = leanh::lean_ctor_get_uint64(
                        v_a_3724_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3728_ = v_hash_3743_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3729_ = 32u64;
                v___x_3730_ = lean_uint64_shift_right(v___y_3728_, v___x_3729_);
                v_fold_3731_ = lean_uint64_xor(v___y_3728_, v___x_3730_);
                v___x_3732_ = 16u64;
                v___x_3733_ = lean_uint64_shift_right(v_fold_3731_, v___x_3732_);
                v___x_3734_ = lean_uint64_xor(v_fold_3731_, v___x_3733_);
                v___x_3735_ = lean_uint64_to_usize(v___x_3734_);
                v___x_3736_ = lean_usize_of_nat(v___x_3726_);
                v___x_3737_ = 1usize;
                v___x_3738_ = lean_usize_sub(v___x_3736_, v___x_3737_);
                v___x_3739_ = lean_usize_land(v___x_3735_, v___x_3738_);
                v___x_3740_ = lean_array_uget_borrowed(v_buckets_3725_, v___x_3739_);
                v___x_3741_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___redArg(v_a_3724_, v___x_3740_);
                return v___x_3741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg___boxed(
    mut v_m_3744_: *mut leanh::LeanObject,
    mut v_a_3745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(v_m_3744_, v_a_3745_);
    leanh::lean_dec(v_a_3745_);
    leanh::lean_dec_ref(v_m_3744_);
    return v_res_3746_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___redArg(
    mut v_keys_3747_: *mut leanh::LeanObject,
    mut v_i_3748_: *mut leanh::LeanObject,
    mut v_k_3749_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: u8 = 0;
    let mut v_k_x27_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3750_ = lean_array_get_size(v_keys_3747_);
                v___x_3751_ = lean_nat_dec_lt(v_i_3748_, v___x_3750_);
                if v___x_3751_ == 0 {
                    leanh::lean_dec(v_i_3748_);
                    return v___x_3751_;
                } else {
                    v_k_x27_3752_ = lean_array_fget_borrowed(v_keys_3747_, v_i_3748_);
                    v___x_3753_ = l_Lean_instBEqExtraModUse_beq(v_k_3749_, v_k_x27_3752_);
                    if v___x_3753_ == 0 {
                        v___x_3754_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3755_ = lean_nat_add(v_i_3748_, v___x_3754_);
                        leanh::lean_dec(v_i_3748_);
                        v_i_3748_ = v___x_3755_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_3748_);
                        return v___x_3753_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___redArg___boxed(
    mut v_keys_3757_: *mut leanh::LeanObject,
    mut v_i_3758_: *mut leanh::LeanObject,
    mut v_k_3759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3760_: u8 = 0;
    let mut v_r_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3760_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___redArg(v_keys_3757_, v_i_3758_, v_k_3759_);
    leanh::lean_dec_ref(v_k_3759_);
    leanh::lean_dec_ref(v_keys_3757_);
    v_r_3761_ = leanh::lean_box((v_res_3760_) as usize);
    return v_r_3761_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___redArg(
    mut v_x_3762_: *mut leanh::LeanObject,
    mut v_x_3763_: usize,
    mut v_x_3764_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: usize = 0;
    let mut v___x_3768_: usize = 0;
    let mut v___x_3769_: usize = 0;
    let mut v_j_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: u8 = 0;
    let mut v_node_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: usize = 0;
    let mut v___x_3777_: u8 = 0;
    let mut v_ks_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3762_) == 0 {
                    v_es_3765_ = leanh::lean_ctor_get(v_x_3762_, 0);
                    v___x_3766_ = leanh::lean_box(2);
                    v___x_3767_ = 5usize;
                    v___x_3768_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_3769_ = lean_usize_land(v_x_3763_, v___x_3768_);
                    v_j_3770_ = lean_usize_to_nat(v___x_3769_);
                    v___x_3771_ = lean_array_get_borrowed(v___x_3766_, v_es_3765_, v_j_3770_);
                    leanh::lean_dec(v_j_3770_);
                    match leanh::lean_obj_tag(v___x_3771_) {
                        0 => {
                            v_key_3772_ = leanh::lean_ctor_get(v___x_3771_, 0);
                            v___x_3773_ = l_Lean_instBEqExtraModUse_beq(v_x_3764_, v_key_3772_);
                            return v___x_3773_;
                        }
                        1 => {
                            v_node_3774_ = leanh::lean_ctor_get(v___x_3771_, 0);
                            v___x_3775_ = lean_usize_shift_right(v_x_3763_, v___x_3767_);
                            v_x_3762_ = v_node_3774_;
                            v_x_3763_ = v___x_3775_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3777_ = 0;
                            return v___x_3777_;
                        }
                    }
                } else {
                    v_ks_3778_ = leanh::lean_ctor_get(v_x_3762_, 0);
                    v___x_3779_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3780_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___redArg(v_ks_3778_, v___x_3779_, v_x_3764_);
                    return v___x_3780_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___redArg___boxed(
    mut v_x_3781_: *mut leanh::LeanObject,
    mut v_x_3782_: *mut leanh::LeanObject,
    mut v_x_3783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5089__boxed_3784_: usize = 0;
    let mut v_res_3785_: u8 = 0;
    let mut v_r_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_5089__boxed_3784_ = leanh::lean_unbox_usize(v_x_3782_);
    leanh::lean_dec(v_x_3782_);
    v_res_3785_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___redArg(v_x_3781_, v_x_5089__boxed_3784_, v_x_3783_);
    leanh::lean_dec_ref(v_x_3783_);
    leanh::lean_dec_ref(v_x_3781_);
    v_r_3786_ = leanh::lean_box((v_res_3785_) as usize);
    return v_r_3786_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___redArg(
    mut v_x_3787_: *mut leanh::LeanObject,
    mut v_x_3788_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3789_: u64 = 0;
    let mut v___x_3790_: usize = 0;
    let mut v___x_3791_: u8 = 0;
    v___x_3789_ = l_Lean_instHashableExtraModUse_hash(v_x_3788_);
    v___x_3790_ = lean_uint64_to_usize(v___x_3789_);
    v___x_3791_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___redArg(v_x_3787_, v___x_3790_, v_x_3788_);
    return v___x_3791_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_x_3792_: *mut leanh::LeanObject,
    mut v_x_3793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3794_: u8 = 0;
    let mut v_r_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3794_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___redArg(v_x_3792_, v_x_3793_);
    leanh::lean_dec_ref(v_x_3793_);
    leanh::lean_dec_ref(v_x_3792_);
    v_r_3795_ = leanh::lean_box((v_res_3794_) as usize);
    return v_r_3795_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0()
-> f64 {
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: f64 = 0.0;
    v___x_3796_ = leanh::lean_unsigned_to_nat(0);
    v___x_3797_ = lean_float_of_nat(v___x_3796_);
    return v___x_3797_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7(
    mut v_cls_3801_: *mut leanh::LeanObject,
    mut v_msg_3802_: *mut leanh::LeanObject,
    mut v___y_3803_: *mut leanh::LeanObject,
    mut v___y_3804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3824_: u8 = 0;
    let mut v_tid_3825_: u64 = 0;
    let mut v_traces_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3829_: u8 = 0;
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: f64 = 0.0;
    let mut v___x_3832_: u8 = 0;
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3806_ = leanh::lean_ctor_get(v___y_3803_, 5);
                v___x_3807_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v_msg_3802_, v___y_3803_, v___y_3804_);
                v_a_3808_ = leanh::lean_ctor_get(v___x_3807_, 0);
                v_isSharedCheck_3852_ = (!leanh::lean_is_exclusive(v___x_3807_)) as u8;
                if v_isSharedCheck_3852_ == 0 {
                    v___x_3810_ = v___x_3807_;
                    v_isShared_3811_ = v_isSharedCheck_3852_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3808_);
                    leanh::lean_dec(v___x_3807_);
                    v___x_3810_ = leanh::lean_box(0);
                    v_isShared_3811_ = v_isSharedCheck_3852_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3812_ = lean_st_ref_take(v___y_3804_);
                v_traceState_3813_ = leanh::lean_ctor_get(v___x_3812_, 4);
                v_env_3814_ = leanh::lean_ctor_get(v___x_3812_, 0);
                v_nextMacroScope_3815_ = leanh::lean_ctor_get(v___x_3812_, 1);
                v_ngen_3816_ = leanh::lean_ctor_get(v___x_3812_, 2);
                v_auxDeclNGen_3817_ = leanh::lean_ctor_get(v___x_3812_, 3);
                v_cache_3818_ = leanh::lean_ctor_get(v___x_3812_, 5);
                v_messages_3819_ = leanh::lean_ctor_get(v___x_3812_, 6);
                v_infoState_3820_ = leanh::lean_ctor_get(v___x_3812_, 7);
                v_snapshotTasks_3821_ = leanh::lean_ctor_get(v___x_3812_, 8);
                v_isSharedCheck_3851_ = (!leanh::lean_is_exclusive(v___x_3812_)) as u8;
                if v_isSharedCheck_3851_ == 0 {
                    v___x_3823_ = v___x_3812_;
                    v_isShared_3824_ = v_isSharedCheck_3851_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3821_);
                    leanh::lean_inc(v_infoState_3820_);
                    leanh::lean_inc(v_messages_3819_);
                    leanh::lean_inc(v_cache_3818_);
                    leanh::lean_inc(v_traceState_3813_);
                    leanh::lean_inc(v_auxDeclNGen_3817_);
                    leanh::lean_inc(v_ngen_3816_);
                    leanh::lean_inc(v_nextMacroScope_3815_);
                    leanh::lean_inc(v_env_3814_);
                    leanh::lean_dec(v___x_3812_);
                    v___x_3823_ = leanh::lean_box(0);
                    v_isShared_3824_ = v_isSharedCheck_3851_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3825_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3813_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3826_ = leanh::lean_ctor_get(v_traceState_3813_, 0);
                v_isSharedCheck_3850_ =
                    (!leanh::lean_is_exclusive(v_traceState_3813_)) as u8;
                if v_isSharedCheck_3850_ == 0 {
                    v___x_3828_ = v_traceState_3813_;
                    v_isShared_3829_ = v_isSharedCheck_3850_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3826_);
                    leanh::lean_dec(v_traceState_3813_);
                    v___x_3828_ = leanh::lean_box(0);
                    v_isShared_3829_ = v_isSharedCheck_3850_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3830_ = leanh::lean_box(0);
                v___x_3831_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0);
                v___x_3832_ = 0;
                v___x_3833_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__1;
                v___x_3834_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_3834_, 0, v_cls_3801_);
                leanh::lean_ctor_set(v___x_3834_, 1, v___x_3830_);
                leanh::lean_ctor_set(v___x_3834_, 2, v___x_3833_);
                leanh::lean_ctor_set_float(
                    v___x_3834_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3831_,
                );
                leanh::lean_ctor_set_float(
                    v___x_3834_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3831_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3834_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3832_,
                );
                v___x_3835_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__2;
                v___x_3836_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3836_, 0, v___x_3834_);
                leanh::lean_ctor_set(v___x_3836_, 1, v_a_3808_);
                leanh::lean_ctor_set(v___x_3836_, 2, v___x_3835_);
                leanh::lean_inc(v_ref_3806_);
                v___x_3837_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3837_, 0, v_ref_3806_);
                leanh::lean_ctor_set(v___x_3837_, 1, v___x_3836_);
                v___x_3838_ = l_Lean_PersistentArray_push___redArg(v_traces_3826_, v___x_3837_);
                if v_isShared_3829_ == 0 {
                    leanh::lean_ctor_set(v___x_3828_, 0, v___x_3838_);
                    v___x_3840_ = v___x_3828_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3849_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3838_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3849_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3825_,
                    );
                    v___x_3840_ = v_reuseFailAlloc_3849_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3824_ == 0 {
                    leanh::lean_ctor_set(v___x_3823_, 4, v___x_3840_);
                    v___x_3842_ = v___x_3823_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_env_3814_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_nextMacroScope_3815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 2, v_ngen_3816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 3, v_auxDeclNGen_3817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 4, v___x_3840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 5, v_cache_3818_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 6, v_messages_3819_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 7, v_infoState_3820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 8, v_snapshotTasks_3821_);
                    v___x_3842_ = v_reuseFailAlloc_3848_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3843_ = lean_st_ref_set(v___y_3804_, v___x_3842_);
                v___x_3844_ = leanh::lean_box(0);
                if v_isShared_3811_ == 0 {
                    leanh::lean_ctor_set(v___x_3810_, 0, v___x_3844_);
                    v___x_3846_ = v___x_3810_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
                    v___x_3846_ = v_reuseFailAlloc_3847_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___boxed(
    mut v_cls_3853_: *mut leanh::LeanObject,
    mut v_msg_3854_: *mut leanh::LeanObject,
    mut v___y_3855_: *mut leanh::LeanObject,
    mut v___y_3856_: *mut leanh::LeanObject,
    mut v___y_3857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3858_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7(v_cls_3853_, v_msg_3854_, v___y_3855_, v___y_3856_);
    leanh::lean_dec(v___y_3856_);
    leanh::lean_dec_ref(v___y_3855_);
    return v_res_3858_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3861_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__1;
    v___x_3862_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__0;
    v___x_3863_ = l_Lean_PersistentHashMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3862_,
        v___x_3861_,
    );
    return v___x_3863_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3868_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__5;
    v___x_3869_ = l_Lean_stringToMessageData(v___x_3868_);
    return v___x_3869_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3871_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__7;
    v___x_3872_ = l_Lean_stringToMessageData(v___x_3871_);
    return v___x_3872_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3873_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__1;
    v___x_3874_ = l_Lean_stringToMessageData(v___x_3873_);
    return v___x_3874_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12()
-> *mut leanh::LeanObject {
    let mut v_cls_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cls_3878_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__4;
    v___x_3879_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__11;
    v___x_3880_ = l_Lean_Name_append(v___x_3879_, v_cls_3878_);
    return v___x_3880_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3882_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__13;
    v___x_3883_ = l_Lean_stringToMessageData(v___x_3882_);
    return v___x_3883_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3885_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__15;
    v___x_3886_ = l_Lean_stringToMessageData(v___x_3885_);
    return v___x_3886_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3(
    mut v_mod_3891_: *mut leanh::LeanObject,
    mut v_isMeta_3892_: u8,
    mut v_hint_3893_: *mut leanh::LeanObject,
    mut v___y_3894_: *mut leanh::LeanObject,
    mut v___y_3895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3899_: u8 = 0;
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3921_: u8 = 0;
    let mut v_asyncMode_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut v_unused_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v_options_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3936_: u8 = 0;
    let mut v_inheritedTraceOptions_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3897_ = lean_st_ref_get(v___y_3895_);
                v_env_3898_ = leanh::lean_ctor_get(v___x_3897_, 0);
                leanh::lean_inc_ref(v_env_3898_);
                leanh::lean_dec(v___x_3897_);
                v_isExporting_3899_ = leanh::lean_ctor_get_uint8(
                    v_env_3898_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_3898_);
                v___x_3900_ = lean_st_ref_get(v___y_3895_);
                v_env_3901_ = leanh::lean_ctor_get(v___x_3900_, 0);
                leanh::lean_inc_ref(v_env_3901_);
                leanh::lean_dec(v___x_3900_);
                v___x_3902_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2);
                leanh::lean_inc(v_mod_3891_);
                v_entry_3903_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                leanh::lean_ctor_set(v_entry_3903_, 0, v_mod_3891_);
                leanh::lean_ctor_set_uint8(
                    v_entry_3903_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_isExporting_3899_,
                );
                leanh::lean_ctor_set_uint8(
                    v_entry_3903_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_3892_,
                );
                v___x_3904_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_3905_ = leanh::lean_box(1);
                v___x_3906_ = leanh::lean_box(0);
                v___x_3933_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_3902_,
                    v___x_3904_,
                    v_env_3901_,
                    v___x_3905_,
                    v___x_3906_,
                );
                v___x_3934_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___redArg(v___x_3933_, v_entry_3903_);
                leanh::lean_dec(v___x_3933_);
                if v___x_3934_ == 0 {
                    v_options_3935_ = leanh::lean_ctor_get(v___y_3894_, 2);
                    v_hasTrace_3936_ = leanh::lean_ctor_get_uint8(
                        v_options_3935_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3936_ == 0 {
                        leanh::lean_dec(v_hint_3893_);
                        leanh::lean_dec(v_mod_3891_);
                        v___y_3908_ = v___y_3895_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_3937_ =
                            leanh::lean_ctor_get(v___y_3894_, 13);
                        v_cls_3938_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__4;
                        v___x_3958_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12);
                        v___x_3959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3937_,
                            v_options_3935_,
                            v___x_3958_,
                        );
                        if v___x_3959_ == 0 {
                            leanh::lean_dec(v_hint_3893_);
                            leanh::lean_dec(v_mod_3891_);
                            v___y_3908_ = v___y_3895_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3960_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14);
                            if v_isExporting_3899_ == 0 {
                                v___x_3969_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__19;
                                v___y_3962_ = v___x_3969_;
                                state = 6;
                                continue;
                            } else {
                                v___x_3970_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__20;
                                v___y_3962_ = v___x_3970_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v_entry_3903_, 1);
                    leanh::lean_dec(v_hint_3893_);
                    leanh::lean_dec(v_mod_3891_);
                    v___x_3971_ = leanh::lean_box(0);
                    v___x_3972_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3972_, 0, v___x_3971_);
                    return v___x_3972_;
                }
            }
            1 => {
                v___x_3909_ = lean_st_ref_take(v___y_3908_);
                v_toEnvExtension_3910_ = leanh::lean_ctor_get(v___x_3904_, 0);
                v_env_3911_ = leanh::lean_ctor_get(v___x_3909_, 0);
                v_nextMacroScope_3912_ = leanh::lean_ctor_get(v___x_3909_, 1);
                v_ngen_3913_ = leanh::lean_ctor_get(v___x_3909_, 2);
                v_auxDeclNGen_3914_ = leanh::lean_ctor_get(v___x_3909_, 3);
                v_traceState_3915_ = leanh::lean_ctor_get(v___x_3909_, 4);
                v_messages_3916_ = leanh::lean_ctor_get(v___x_3909_, 6);
                v_infoState_3917_ = leanh::lean_ctor_get(v___x_3909_, 7);
                v_snapshotTasks_3918_ = leanh::lean_ctor_get(v___x_3909_, 8);
                v_isSharedCheck_3931_ = (!leanh::lean_is_exclusive(v___x_3909_)) as u8;
                if v_isSharedCheck_3931_ == 0 {
                    v_unused_3932_ = leanh::lean_ctor_get(v___x_3909_, 5);
                    leanh::lean_dec(v_unused_3932_);
                    v___x_3920_ = v___x_3909_;
                    v_isShared_3921_ = v_isSharedCheck_3931_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3918_);
                    leanh::lean_inc(v_infoState_3917_);
                    leanh::lean_inc(v_messages_3916_);
                    leanh::lean_inc(v_traceState_3915_);
                    leanh::lean_inc(v_auxDeclNGen_3914_);
                    leanh::lean_inc(v_ngen_3913_);
                    leanh::lean_inc(v_nextMacroScope_3912_);
                    leanh::lean_inc(v_env_3911_);
                    leanh::lean_dec(v___x_3909_);
                    v___x_3920_ = leanh::lean_box(0);
                    v_isShared_3921_ = v_isSharedCheck_3931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_3922_ = leanh::lean_ctor_get(v_toEnvExtension_3910_, 2);
                v___x_3923_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3904_,
                    v_env_3911_,
                    v_entry_3903_,
                    v_asyncMode_3922_,
                    v___x_3906_,
                );
                v___x_3924_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2);
                if v_isShared_3921_ == 0 {
                    leanh::lean_ctor_set(v___x_3920_, 5, v___x_3924_);
                    leanh::lean_ctor_set(v___x_3920_, 0, v___x_3923_);
                    v___x_3926_ = v___x_3920_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_nextMacroScope_3912_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 2, v_ngen_3913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 3, v_auxDeclNGen_3914_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 4, v_traceState_3915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 5, v___x_3924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 6, v_messages_3916_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 7, v_infoState_3917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 8, v_snapshotTasks_3918_);
                    v___x_3926_ = v_reuseFailAlloc_3930_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3927_ = lean_st_ref_set(v___y_3908_, v___x_3926_);
                v___x_3928_ = leanh::lean_box(0);
                v___x_3929_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3929_, 0, v___x_3928_);
                return v___x_3929_;
            }
            4 => {
                v___x_3942_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3942_, 0, v___y_3940_);
                leanh::lean_ctor_set(v___x_3942_, 1, v___y_3941_);
                v___x_3943_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7(v_cls_3938_, v___x_3942_, v___y_3894_, v___y_3895_);
                if leanh::lean_obj_tag(v___x_3943_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3943_, 1);
                    v___y_3908_ = v___y_3895_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_entry_3903_, 1);
                    return v___x_3943_;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___y_3946_);
                v___x_3947_ = l_Lean_stringToMessageData(v___y_3946_);
                v___x_3948_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3948_, 0, v___y_3945_);
                leanh::lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                v___x_3949_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6);
                v___x_3950_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                leanh::lean_ctor_set(v___x_3950_, 1, v___x_3949_);
                v___x_3951_ = l_Lean_MessageData_ofName(v_mod_3891_);
                v___x_3952_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3952_, 0, v___x_3950_);
                leanh::lean_ctor_set(v___x_3952_, 1, v___x_3951_);
                v___x_3953_ = l_Lean_Name_isAnonymous(v_hint_3893_);
                if v___x_3953_ == 0 {
                    v___x_3954_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8);
                    v___x_3955_ = l_Lean_MessageData_ofName(v_hint_3893_);
                    v___x_3956_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3956_, 0, v___x_3954_);
                    leanh::lean_ctor_set(v___x_3956_, 1, v___x_3955_);
                    v___y_3940_ = v___x_3952_;
                    v___y_3941_ = v___x_3956_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_hint_3893_);
                    v___x_3957_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9);
                    v___y_3940_ = v___x_3952_;
                    v___y_3941_ = v___x_3957_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v___y_3962_);
                v___x_3963_ = l_Lean_stringToMessageData(v___y_3962_);
                v___x_3964_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3964_, 0, v___x_3960_);
                leanh::lean_ctor_set(v___x_3964_, 1, v___x_3963_);
                v___x_3965_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16);
                v___x_3966_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3966_, 0, v___x_3964_);
                leanh::lean_ctor_set(v___x_3966_, 1, v___x_3965_);
                if v_isMeta_3892_ == 0 {
                    v___x_3967_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__17;
                    v___y_3945_ = v___x_3966_;
                    v___y_3946_ = v___x_3967_;
                    state = 5;
                    continue;
                } else {
                    v___x_3968_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__18;
                    v___y_3945_ = v___x_3966_;
                    v___y_3946_ = v___x_3968_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___boxed(
    mut v_mod_3973_: *mut leanh::LeanObject,
    mut v_isMeta_3974_: *mut leanh::LeanObject,
    mut v_hint_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_3979_: u8 = 0;
    let mut v_res_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3979_ = (leanh::lean_unbox(v_isMeta_3974_) as u8);
    v_res_3980_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3(v_mod_3973_, v_isMeta_boxed_3979_, v_hint_3975_, v___y_3976_, v___y_3977_);
    leanh::lean_dec(v___y_3977_);
    leanh::lean_dec_ref(v___y_3976_);
    return v_res_3980_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__4(
    mut v___x_3981_: *mut leanh::LeanObject,
    mut v_declName_3982_: *mut leanh::LeanObject,
    mut v_as_3983_: *mut leanh::LeanObject,
    mut v_sz_3984_: usize,
    mut v_i_3985_: usize,
    mut v_b_3986_: *mut leanh::LeanObject,
    mut v___y_3987_: *mut leanh::LeanObject,
    mut v___y_3988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3990_: u8 = 0;
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: u8 = 0;
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: usize = 0;
    let mut v___x_4003_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3990_ = lean_usize_dec_lt(v_i_3985_, v_sz_3984_);
                if v___x_3990_ == 0 {
                    leanh::lean_dec(v_declName_3982_);
                    v___x_3991_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3991_, 0, v_b_3986_);
                    return v___x_3991_;
                } else {
                    v___x_3992_ = l_Lean_Environment_header(v___x_3981_);
                    v_modules_3993_ = leanh::lean_ctor_get(v___x_3992_, 3);
                    leanh::lean_inc_ref(v_modules_3993_);
                    leanh::lean_dec_ref(v___x_3992_);
                    v___x_3994_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_3995_ = lean_array_uget_borrowed(v_as_3983_, v_i_3985_);
                    v___x_3996_ = lean_array_get(v___x_3994_, v_modules_3993_, v_a_3995_);
                    leanh::lean_dec_ref(v_modules_3993_);
                    v_toImport_3997_ = leanh::lean_ctor_get(v___x_3996_, 0);
                    leanh::lean_inc_ref(v_toImport_3997_);
                    leanh::lean_dec(v___x_3996_);
                    v_module_3998_ = leanh::lean_ctor_get(v_toImport_3997_, 0);
                    leanh::lean_inc(v_module_3998_);
                    leanh::lean_dec_ref(v_toImport_3997_);
                    v___x_3999_ = 0;
                    leanh::lean_inc(v_declName_3982_);
                    v___x_4000_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3(v_module_3998_, v___x_3999_, v_declName_3982_, v___y_3987_, v___y_3988_);
                    if leanh::lean_obj_tag(v___x_4000_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4000_, 1);
                        v___x_4001_ = leanh::lean_box(0);
                        v___x_4002_ = 1usize;
                        v___x_4003_ = lean_usize_add(v_i_3985_, v___x_4002_);
                        v_i_3985_ = v___x_4003_;
                        v_b_3986_ = v___x_4001_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_declName_3982_);
                        return v___x_4000_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__4___boxed(
    mut v___x_4005_: *mut leanh::LeanObject,
    mut v_declName_4006_: *mut leanh::LeanObject,
    mut v_as_4007_: *mut leanh::LeanObject,
    mut v_sz_4008_: *mut leanh::LeanObject,
    mut v_i_4009_: *mut leanh::LeanObject,
    mut v_b_4010_: *mut leanh::LeanObject,
    mut v___y_4011_: *mut leanh::LeanObject,
    mut v___y_4012_: *mut leanh::LeanObject,
    mut v___y_4013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4014_: usize = 0;
    let mut v_i_boxed_4015_: usize = 0;
    let mut v_res_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4014_ = leanh::lean_unbox_usize(v_sz_4008_);
    leanh::lean_dec(v_sz_4008_);
    v_i_boxed_4015_ = leanh::lean_unbox_usize(v_i_4009_);
    leanh::lean_dec(v_i_4009_);
    v_res_4016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__4(v___x_4005_, v_declName_4006_, v_as_4007_, v_sz_boxed_4014_, v_i_boxed_4015_, v_b_4010_, v___y_4011_, v___y_4012_);
    leanh::lean_dec(v___y_4012_);
    leanh::lean_dec_ref(v___y_4011_);
    leanh::lean_dec_ref(v_as_4007_);
    leanh::lean_dec_ref(v___x_4005_);
    return v_res_4016_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4019_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__1;
    v___x_4020_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__0;
    v___x_4021_ = l_Std_HashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4020_,
        v___x_4019_,
    );
    return v___x_4021_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1(
    mut v_declName_4024_: *mut leanh::LeanObject,
    mut v_isMeta_4025_: u8,
    mut v___y_4026_: *mut leanh::LeanObject,
    mut v___y_4027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4037_: usize = 0;
    let mut v___x_4038_: usize = 0;
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4042_: u8 = 0;
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4046_: u8 = 0;
    let mut v_unused_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: u8 = 0;
    let mut v_toImport_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    let mut v___x_4071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4029_ = lean_st_ref_get(v___y_4027_);
                v_env_4033_ = leanh::lean_ctor_get(v___x_4029_, 0);
                leanh::lean_inc_ref(v_env_4033_);
                leanh::lean_dec(v___x_4029_);
                v___x_4048_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4033_, v_declName_4024_);
                if leanh::lean_obj_tag(v___x_4048_) == 0 {
                    leanh::lean_dec_ref(v_env_4033_);
                    leanh::lean_dec(v_declName_4024_);
                    state = 1;
                    continue;
                } else {
                    v_val_4049_ = leanh::lean_ctor_get(v___x_4048_, 0);
                    leanh::lean_inc(v_val_4049_);
                    leanh::lean_dec_ref_known(v___x_4048_, 1);
                    v___x_4050_ = l_Lean_Environment_header(v_env_4033_);
                    v_modules_4051_ = leanh::lean_ctor_get(v___x_4050_, 3);
                    leanh::lean_inc_ref(v_modules_4051_);
                    leanh::lean_dec_ref(v___x_4050_);
                    v___x_4052_ = lean_array_get_size(v_modules_4051_);
                    v___x_4053_ = lean_nat_dec_lt(v_val_4049_, v___x_4052_);
                    if v___x_4053_ == 0 {
                        leanh::lean_dec_ref(v_modules_4051_);
                        leanh::lean_dec(v_val_4049_);
                        leanh::lean_dec_ref(v_env_4033_);
                        leanh::lean_dec(v_declName_4024_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4054_ = lean_st_ref_get(v___y_4027_);
                        v_env_4055_ = leanh::lean_ctor_get(v___x_4054_, 0);
                        leanh::lean_inc_ref(v_env_4055_);
                        leanh::lean_dec(v___x_4054_);
                        v___x_4056_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2);
                        v___x_4057_ = lean_array_fget(v_modules_4051_, v_val_4049_);
                        leanh::lean_dec(v_val_4049_);
                        leanh::lean_dec_ref(v_modules_4051_);
                        if v_isMeta_4025_ == 0 {
                            leanh::lean_dec_ref(v_env_4055_);
                            v___y_4059_ = v_isMeta_4025_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_declName_4024_);
                            v___x_4070_ = l_Lean_isMarkedMeta(v_env_4055_, v_declName_4024_);
                            if v___x_4070_ == 0 {
                                v___y_4059_ = v_isMeta_4025_;
                                state = 5;
                                continue;
                            } else {
                                v___x_4071_ = 0;
                                v___y_4059_ = v___x_4071_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4031_ = leanh::lean_box(0);
                v___x_4032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4032_, 0, v___x_4031_);
                return v___x_4032_;
            }
            2 => {
                v___x_4036_ = leanh::lean_box(0);
                v_sz_4037_ = lean_array_size(v___y_4035_);
                v___x_4038_ = 0usize;
                v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__4(v_env_4033_, v_declName_4024_, v___y_4035_, v_sz_4037_, v___x_4038_, v___x_4036_, v___y_4026_, v___y_4027_);
                leanh::lean_dec_ref(v___y_4035_);
                leanh::lean_dec_ref(v_env_4033_);
                if leanh::lean_obj_tag(v___x_4039_) == 0 {
                    v_isSharedCheck_4046_ = (!leanh::lean_is_exclusive(v___x_4039_)) as u8;
                    if v_isSharedCheck_4046_ == 0 {
                        v_unused_4047_ = leanh::lean_ctor_get(v___x_4039_, 0);
                        leanh::lean_dec(v_unused_4047_);
                        v___x_4041_ = v___x_4039_;
                        v_isShared_4042_ = v_isSharedCheck_4046_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4039_);
                        v___x_4041_ = leanh::lean_box(0);
                        v_isShared_4042_ = v_isSharedCheck_4046_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4039_;
                }
            }
            3 => {
                if v_isShared_4042_ == 0 {
                    leanh::lean_ctor_set(v___x_4041_, 0, v___x_4036_);
                    v___x_4044_ = v___x_4041_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4045_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4036_);
                    v___x_4044_ = v_reuseFailAlloc_4045_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4044_;
            }
            5 => {
                v_toImport_4060_ = leanh::lean_ctor_get(v___x_4057_, 0);
                leanh::lean_inc_ref(v_toImport_4060_);
                leanh::lean_dec(v___x_4057_);
                v_module_4061_ = leanh::lean_ctor_get(v_toImport_4060_, 0);
                leanh::lean_inc(v_module_4061_);
                leanh::lean_dec_ref(v_toImport_4060_);
                leanh::lean_inc(v_declName_4024_);
                v___x_4062_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3(v_module_4061_, v___y_4059_, v_declName_4024_, v___y_4026_, v___y_4027_);
                if leanh::lean_obj_tag(v___x_4062_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4062_, 1);
                    v___x_4063_ = l_Lean_indirectModUseExt;
                    v___x_4064_ = leanh::lean_box(1);
                    v___x_4065_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_env_4033_);
                    v___x_4066_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4056_,
                        v___x_4063_,
                        v_env_4033_,
                        v___x_4064_,
                        v___x_4065_,
                    );
                    v___x_4067_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(v___x_4066_, v_declName_4024_);
                    leanh::lean_dec(v___x_4066_);
                    if leanh::lean_obj_tag(v___x_4067_) == 0 {
                        v___x_4068_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__3;
                        v___y_4035_ = v___x_4068_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4069_ = leanh::lean_ctor_get(v___x_4067_, 0);
                        leanh::lean_inc(v_val_4069_);
                        leanh::lean_dec_ref_known(v___x_4067_, 1);
                        v___y_4035_ = v_val_4069_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4033_);
                    leanh::lean_dec(v_declName_4024_);
                    return v___x_4062_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___boxed(
    mut v_declName_4072_: *mut leanh::LeanObject,
    mut v_isMeta_4073_: *mut leanh::LeanObject,
    mut v___y_4074_: *mut leanh::LeanObject,
    mut v___y_4075_: *mut leanh::LeanObject,
    mut v___y_4076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_4077_: u8 = 0;
    let mut v_res_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4077_ = (leanh::lean_unbox(v_isMeta_4073_) as u8);
    v_res_4078_ =
        l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1(
            v_declName_4072_,
            v_isMeta_boxed_4077_,
            v___y_4074_,
            v___y_4075_,
        );
    leanh::lean_dec(v___y_4075_);
    leanh::lean_dec_ref(v___y_4074_);
    return v_res_4078_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_keys_4079_: *mut leanh::LeanObject,
    mut v_vals_4080_: *mut leanh::LeanObject,
    mut v_i_4081_: *mut leanh::LeanObject,
    mut v_k_4082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4083_ = lean_array_get_size(v_keys_4079_);
                v___x_4084_ = lean_nat_dec_lt(v_i_4081_, v___x_4083_);
                if v___x_4084_ == 0 {
                    leanh::lean_dec(v_i_4081_);
                    v___x_4085_ = leanh::lean_box(0);
                    return v___x_4085_;
                } else {
                    v_k_x27_4086_ = lean_array_fget_borrowed(v_keys_4079_, v_i_4081_);
                    v___x_4087_ = lean_name_eq(v_k_4082_, v_k_x27_4086_);
                    if v___x_4087_ == 0 {
                        v___x_4088_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4089_ = lean_nat_add(v_i_4081_, v___x_4088_);
                        leanh::lean_dec(v_i_4081_);
                        v_i_4081_ = v___x_4089_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4091_ = lean_array_fget_borrowed(v_vals_4080_, v_i_4081_);
                        leanh::lean_dec(v_i_4081_);
                        leanh::lean_inc(v___x_4091_);
                        v___x_4092_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4092_, 0, v___x_4091_);
                        return v___x_4092_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_keys_4093_: *mut leanh::LeanObject,
    mut v_vals_4094_: *mut leanh::LeanObject,
    mut v_i_4095_: *mut leanh::LeanObject,
    mut v_k_4096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_4093_, v_vals_4094_, v_i_4095_, v_k_4096_);
    leanh::lean_dec(v_k_4096_);
    leanh::lean_dec_ref(v_vals_4094_);
    leanh::lean_dec_ref(v_keys_4093_);
    return v_res_4097_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_x_4098_: *mut leanh::LeanObject,
    mut v_x_4099_: usize,
    mut v_x_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: usize = 0;
    let mut v___x_4104_: usize = 0;
    let mut v___x_4105_: usize = 0;
    let mut v_j_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: usize = 0;
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4098_) == 0 {
                    v_es_4101_ = leanh::lean_ctor_get(v_x_4098_, 0);
                    v___x_4102_ = leanh::lean_box(2);
                    v___x_4103_ = 5usize;
                    v___x_4104_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4105_ = lean_usize_land(v_x_4099_, v___x_4104_);
                    v_j_4106_ = lean_usize_to_nat(v___x_4105_);
                    v___x_4107_ = lean_array_get_borrowed(v___x_4102_, v_es_4101_, v_j_4106_);
                    leanh::lean_dec(v_j_4106_);
                    match leanh::lean_obj_tag(v___x_4107_) {
                        0 => {
                            v_key_4108_ = leanh::lean_ctor_get(v___x_4107_, 0);
                            v_val_4109_ = leanh::lean_ctor_get(v___x_4107_, 1);
                            v___x_4110_ = lean_name_eq(v_x_4100_, v_key_4108_);
                            if v___x_4110_ == 0 {
                                v___x_4111_ = leanh::lean_box(0);
                                return v___x_4111_;
                            } else {
                                leanh::lean_inc(v_val_4109_);
                                v___x_4112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4112_, 0, v_val_4109_);
                                return v___x_4112_;
                            }
                        }
                        1 => {
                            v_node_4113_ = leanh::lean_ctor_get(v___x_4107_, 0);
                            v___x_4114_ = lean_usize_shift_right(v_x_4099_, v___x_4103_);
                            v_x_4098_ = v_node_4113_;
                            v_x_4099_ = v___x_4114_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4116_ = leanh::lean_box(0);
                            return v___x_4116_;
                        }
                    }
                } else {
                    v_ks_4117_ = leanh::lean_ctor_get(v_x_4098_, 0);
                    v_vs_4118_ = leanh::lean_ctor_get(v_x_4098_, 1);
                    v___x_4119_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4120_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___redArg(v_ks_4117_, v_vs_4118_, v___x_4119_, v_x_4100_);
                    return v___x_4120_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4121_: *mut leanh::LeanObject,
    mut v_x_4122_: *mut leanh::LeanObject,
    mut v_x_4123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5639__boxed_4124_: usize = 0;
    let mut v_res_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_5639__boxed_4124_ = leanh::lean_unbox_usize(v_x_4122_);
    leanh::lean_dec(v_x_4122_);
    v_res_4125_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___redArg(v_x_4121_, v_x_5639__boxed_4124_, v_x_4123_);
    leanh::lean_dec(v_x_4123_);
    leanh::lean_dec_ref(v_x_4121_);
    return v_res_4125_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___redArg(
    mut v_x_4126_: *mut leanh::LeanObject,
    mut v_x_4127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4129_: u64 = 0;
    let mut v___x_4130_: usize = 0;
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: u64 = 0;
    let mut v_hash_4133_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4127_) == 0 {
                    v___x_4132_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_4129_ = v___x_4132_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4133_ = leanh::lean_ctor_get_uint64(
                        v_x_4127_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4129_ = v_hash_4133_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4130_ = lean_uint64_to_usize(v___y_4129_);
                v___x_4131_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___redArg(v_x_4126_, v___x_4130_, v_x_4127_);
                return v___x_4131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_4134_: *mut leanh::LeanObject,
    mut v_x_4135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4136_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___redArg(v_x_4134_, v_x_4135_);
    leanh::lean_dec(v_x_4135_);
    leanh::lean_dec_ref(v_x_4134_);
    return v_res_4136_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___redArg(
    mut v_x_4137_: *mut leanh::LeanObject,
    mut v_x_4138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_4139_: u8 = 0;
    v_stage_u2081_4139_ = leanh::lean_ctor_get_uint8(
        v_x_4137_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_4139_ == 0 {
        let mut v_map_u2081_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_4140_ = leanh::lean_ctor_get(v_x_4137_, 0);
        v_map_u2082_4141_ = leanh::lean_ctor_get(v_x_4137_, 1);
        v___x_4142_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___redArg(v_map_u2082_4141_, v_x_4138_);
        if leanh::lean_obj_tag(v___x_4142_) == 0 {
            let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(v_map_u2081_4140_, v_x_4138_);
            return v___x_4143_;
        } else {
            return v___x_4142_;
        }
    } else {
        let mut v_map_u2081_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_4144_ = leanh::lean_ctor_get(v_x_4137_, 0);
        v___x_4145_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(v_map_u2081_4144_, v_x_4138_);
        return v___x_4145_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___redArg___boxed(
    mut v_x_4146_: *mut leanh::LeanObject,
    mut v_x_4147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4148_ =
        l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___redArg(
            v_x_4146_, v_x_4147_,
        );
    leanh::lean_dec(v_x_4147_);
    leanh::lean_dec_ref(v_x_4146_);
    return v_res_4148_;
}
pub unsafe fn l_Lean_Compiler_CSimp_replaceConstant_x3f(
    mut v_env_4149_: *mut leanh::LeanObject,
    mut v_e_4150_: *mut leanh::LeanObject,
    mut v_a_4151_: *mut leanh::LeanObject,
    mut v_a_4152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4166_: u8 = 0;
    let mut v_toDeclName_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_thmName_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: u8 = 0;
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: u8 = 0;
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v_unused_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4190_: u8 = 0;
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4194_: u8 = 0;
    let mut v_isSharedCheck_4195_: u8 = 0;
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_4150_) == 4 {
                    v_declName_4154_ = leanh::lean_ctor_get(v_e_4150_, 0);
                    v___x_4155_ = l_Lean_Compiler_CSimp_ext;
                    v_ext_4156_ = leanh::lean_ctor_get(v___x_4155_, 1);
                    v_toEnvExtension_4157_ = leanh::lean_ctor_get(v_ext_4156_, 0);
                    v_asyncMode_4158_ = leanh::lean_ctor_get(v_toEnvExtension_4157_, 2);
                    v___x_4159_ = l_Lean_Compiler_CSimp_instInhabitedState_default;
                    v_s_4160_ = l_Lean_ScopedEnvExtension_getState___redArg(
                        v___x_4159_,
                        v___x_4155_,
                        v_env_4149_,
                        v_asyncMode_4158_,
                    );
                    v_map_4161_ = leanh::lean_ctor_get(v_s_4160_, 0);
                    leanh::lean_inc_ref(v_map_4161_);
                    leanh::lean_dec(v_s_4160_);
                    v___x_4162_ = l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___redArg(v_map_4161_, v_declName_4154_);
                    leanh::lean_dec_ref(v_map_4161_);
                    if leanh::lean_obj_tag(v___x_4162_) == 1 {
                        v_val_4163_ = leanh::lean_ctor_get(v___x_4162_, 0);
                        v_isSharedCheck_4195_ =
                            (!leanh::lean_is_exclusive(v___x_4162_)) as u8;
                        if v_isSharedCheck_4195_ == 0 {
                            v___x_4165_ = v___x_4162_;
                            v_isShared_4166_ = v_isSharedCheck_4195_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4163_);
                            leanh::lean_dec(v___x_4162_);
                            v___x_4165_ = leanh::lean_box(0);
                            v_isShared_4166_ = v_isSharedCheck_4195_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4162_);
                        v___x_4196_ = leanh::lean_box(0);
                        v___x_4197_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4197_, 0, v___x_4196_);
                        return v___x_4197_;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4149_);
                    v___x_4198_ = leanh::lean_box(0);
                    v___x_4199_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4199_, 0, v___x_4198_);
                    return v___x_4199_;
                }
            }
            1 => {
                v_toDeclName_4167_ = leanh::lean_ctor_get(v_val_4163_, 1);
                leanh::lean_inc(v_toDeclName_4167_);
                v_thmName_4168_ = leanh::lean_ctor_get(v_val_4163_, 2);
                leanh::lean_inc(v_thmName_4168_);
                leanh::lean_dec(v_val_4163_);
                v___x_4169_ = 0;
                v___x_4170_ = leanh::lean_box((v___x_4169_) as usize);
                v___x_4171_ = leanh::lean_alloc_closure(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___boxed as *mut core::ffi::c_void, 5, 2);
                leanh::lean_closure_set(v___x_4171_, 0, v_thmName_4168_);
                leanh::lean_closure_set(v___x_4171_, 1, v___x_4170_);
                v___x_4172_ = 1;
                v___x_4173_ = l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___redArg(v___x_4171_, v___x_4172_, v_a_4151_, v_a_4152_);
                if leanh::lean_obj_tag(v___x_4173_) == 0 {
                    v_isSharedCheck_4185_ = (!leanh::lean_is_exclusive(v___x_4173_)) as u8;
                    if v_isSharedCheck_4185_ == 0 {
                        v_unused_4186_ = leanh::lean_ctor_get(v___x_4173_, 0);
                        leanh::lean_dec(v_unused_4186_);
                        v___x_4175_ = v___x_4173_;
                        v_isShared_4176_ = v_isSharedCheck_4185_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4173_);
                        v___x_4175_ = leanh::lean_box(0);
                        v_isShared_4176_ = v_isSharedCheck_4185_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_toDeclName_4167_);
                    leanh::lean_del_object(v___x_4165_);
                    v_a_4187_ = leanh::lean_ctor_get(v___x_4173_, 0);
                    v_isSharedCheck_4194_ = (!leanh::lean_is_exclusive(v___x_4173_)) as u8;
                    if v_isSharedCheck_4194_ == 0 {
                        v___x_4189_ = v___x_4173_;
                        v_isShared_4190_ = v_isSharedCheck_4194_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4187_);
                        leanh::lean_dec(v___x_4173_);
                        v___x_4189_ = leanh::lean_box(0);
                        v_isShared_4190_ = v_isSharedCheck_4194_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4177_ = l_Lean_Expr_constLevels_x21(v_e_4150_);
                v___x_4178_ = l_Lean_mkConst(v_toDeclName_4167_, v___x_4177_);
                if v_isShared_4166_ == 0 {
                    leanh::lean_ctor_set(v___x_4165_, 0, v___x_4178_);
                    v___x_4180_ = v___x_4165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4184_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4178_);
                    v___x_4180_ = v_reuseFailAlloc_4184_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4176_ == 0 {
                    leanh::lean_ctor_set(v___x_4175_, 0, v___x_4180_);
                    v___x_4182_ = v___x_4175_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4183_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4180_);
                    v___x_4182_ = v_reuseFailAlloc_4183_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4182_;
            }
            5 => {
                if v_isShared_4190_ == 0 {
                    v___x_4192_ = v___x_4189_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4193_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
                    v___x_4192_ = v_reuseFailAlloc_4193_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_CSimp_replaceConstant_x3f___boxed(
    mut v_env_4200_: *mut leanh::LeanObject,
    mut v_e_4201_: *mut leanh::LeanObject,
    mut v_a_4202_: *mut leanh::LeanObject,
    mut v_a_4203_: *mut leanh::LeanObject,
    mut v_a_4204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4205_ =
        l_Lean_Compiler_CSimp_replaceConstant_x3f(v_env_4200_, v_e_4201_, v_a_4202_, v_a_4203_);
    leanh::lean_dec(v_a_4203_);
    leanh::lean_dec_ref(v_a_4202_);
    leanh::lean_dec_ref(v_e_4201_);
    return v_res_4205_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0(
    mut v_00_u03b2_4206_: *mut leanh::LeanObject,
    mut v_x_4207_: *mut leanh::LeanObject,
    mut v_x_4208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4209_ =
        l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___redArg(
            v_x_4207_, v_x_4208_,
        );
    return v___x_4209_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___boxed(
    mut v_00_u03b2_4210_: *mut leanh::LeanObject,
    mut v_x_4211_: *mut leanh::LeanObject,
    mut v_x_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4213_ = l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0(
        v_00_u03b2_4210_,
        v_x_4211_,
        v_x_4212_,
    );
    leanh::lean_dec(v_x_4212_);
    leanh::lean_dec_ref(v_x_4211_);
    return v_res_4213_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6(
    mut v_00_u03b1_4214_: *mut leanh::LeanObject,
    mut v_x_4215_: *mut leanh::LeanObject,
    mut v_isExporting_4216_: u8,
    mut v___y_4217_: *mut leanh::LeanObject,
    mut v___y_4218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4220_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg(v_x_4215_, v_isExporting_4216_, v___y_4217_, v___y_4218_);
    return v___x_4220_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___boxed(
    mut v_00_u03b1_4221_: *mut leanh::LeanObject,
    mut v_x_4222_: *mut leanh::LeanObject,
    mut v_isExporting_4223_: *mut leanh::LeanObject,
    mut v___y_4224_: *mut leanh::LeanObject,
    mut v___y_4225_: *mut leanh::LeanObject,
    mut v___y_4226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4227_: u8 = 0;
    let mut v_res_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4227_ = (leanh::lean_unbox(v_isExporting_4223_) as u8);
    v_res_4228_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6(v_00_u03b1_4221_, v_x_4222_, v_isExporting_boxed_4227_, v___y_4224_, v___y_4225_);
    leanh::lean_dec(v___y_4225_);
    leanh::lean_dec_ref(v___y_4224_);
    return v_res_4228_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2(
    mut v_00_u03b1_4229_: *mut leanh::LeanObject,
    mut v_x_4230_: *mut leanh::LeanObject,
    mut v_when_4231_: u8,
    mut v___y_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4235_ =
        l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___redArg(
            v_x_4230_,
            v_when_4231_,
            v___y_4232_,
            v___y_4233_,
        );
    return v___x_4235_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___boxed(
    mut v_00_u03b1_4236_: *mut leanh::LeanObject,
    mut v_x_4237_: *mut leanh::LeanObject,
    mut v_when_4238_: *mut leanh::LeanObject,
    mut v___y_4239_: *mut leanh::LeanObject,
    mut v___y_4240_: *mut leanh::LeanObject,
    mut v___y_4241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_4242_: u8 = 0;
    let mut v_res_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4242_ = (leanh::lean_unbox(v_when_4238_) as u8);
    v_res_4243_ = l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2(
        v_00_u03b1_4236_,
        v_x_4237_,
        v_when_boxed_4242_,
        v___y_4239_,
        v___y_4240_,
    );
    leanh::lean_dec(v___y_4240_);
    leanh::lean_dec_ref(v___y_4239_);
    return v_res_4243_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0(
    mut v_00_u03b2_4244_: *mut leanh::LeanObject,
    mut v_x_4245_: *mut leanh::LeanObject,
    mut v_x_4246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___redArg(v_x_4245_, v_x_4246_);
    return v___x_4247_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4248_: *mut leanh::LeanObject,
    mut v_x_4249_: *mut leanh::LeanObject,
    mut v_x_4250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4251_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0(v_00_u03b2_4248_, v_x_4249_, v_x_4250_);
    leanh::lean_dec(v_x_4250_);
    leanh::lean_dec_ref(v_x_4249_);
    return v_res_4251_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1(
    mut v_00_u03b2_4252_: *mut leanh::LeanObject,
    mut v_m_4253_: *mut leanh::LeanObject,
    mut v_a_4254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(v_m_4253_, v_a_4254_);
    return v___x_4255_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___boxed(
    mut v_00_u03b2_4256_: *mut leanh::LeanObject,
    mut v_m_4257_: *mut leanh::LeanObject,
    mut v_a_4258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1(v_00_u03b2_4256_, v_m_4257_, v_a_4258_);
    leanh::lean_dec(v_a_4258_);
    leanh::lean_dec_ref(v_m_4257_);
    return v_res_4259_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4260_: *mut leanh::LeanObject,
    mut v_x_4261_: *mut leanh::LeanObject,
    mut v_x_4262_: usize,
    mut v_x_4263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4264_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___redArg(v_x_4261_, v_x_4262_, v_x_4263_);
    return v___x_4264_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4265_: *mut leanh::LeanObject,
    mut v_x_4266_: *mut leanh::LeanObject,
    mut v_x_4267_: *mut leanh::LeanObject,
    mut v_x_4268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5851__boxed_4269_: usize = 0;
    let mut v_res_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_5851__boxed_4269_ = leanh::lean_unbox_usize(v_x_4267_);
    leanh::lean_dec(v_x_4267_);
    v_res_4270_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4265_, v_x_4266_, v_x_5851__boxed_4269_, v_x_4268_);
    leanh::lean_dec(v_x_4268_);
    leanh::lean_dec_ref(v_x_4266_);
    return v_res_4270_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4271_: *mut leanh::LeanObject,
    mut v_a_4272_: *mut leanh::LeanObject,
    mut v_x_4273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4274_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___redArg(v_a_4272_, v_x_4273_);
    return v___x_4274_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4275_: *mut leanh::LeanObject,
    mut v_a_4276_: *mut leanh::LeanObject,
    mut v_x_4277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4278_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3(v_00_u03b2_4275_, v_a_4276_, v_x_4277_);
    leanh::lean_dec(v_x_4277_);
    leanh::lean_dec(v_a_4276_);
    return v_res_4278_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6(
    mut v_00_u03b2_4279_: *mut leanh::LeanObject,
    mut v_x_4280_: *mut leanh::LeanObject,
    mut v_x_4281_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4282_: u8 = 0;
    v___x_4282_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___redArg(v_x_4280_, v_x_4281_);
    return v___x_4282_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_4283_: *mut leanh::LeanObject,
    mut v_x_4284_: *mut leanh::LeanObject,
    mut v_x_4285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4286_: u8 = 0;
    let mut v_r_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4286_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6(v_00_u03b2_4283_, v_x_4284_, v_x_4285_);
    leanh::lean_dec_ref(v_x_4285_);
    leanh::lean_dec_ref(v_x_4284_);
    v_r_4287_ = leanh::lean_box((v_res_4286_) as usize);
    return v_r_4287_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b2_4288_: *mut leanh::LeanObject,
    mut v_keys_4289_: *mut leanh::LeanObject,
    mut v_vals_4290_: *mut leanh::LeanObject,
    mut v_heq_4291_: *mut leanh::LeanObject,
    mut v_i_4292_: *mut leanh::LeanObject,
    mut v_k_4293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_4289_, v_vals_4290_, v_i_4292_, v_k_4293_);
    return v___x_4294_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b2_4295_: *mut leanh::LeanObject,
    mut v_keys_4296_: *mut leanh::LeanObject,
    mut v_vals_4297_: *mut leanh::LeanObject,
    mut v_heq_4298_: *mut leanh::LeanObject,
    mut v_i_4299_: *mut leanh::LeanObject,
    mut v_k_4300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4301_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_4295_, v_keys_4296_, v_vals_4297_, v_heq_4298_, v_i_4299_, v_k_4300_);
    leanh::lean_dec(v_k_4300_);
    leanh::lean_dec_ref(v_vals_4297_);
    leanh::lean_dec_ref(v_keys_4296_);
    return v_res_4301_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10(
    mut v_00_u03b2_4302_: *mut leanh::LeanObject,
    mut v_x_4303_: *mut leanh::LeanObject,
    mut v_x_4304_: usize,
    mut v_x_4305_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4306_: u8 = 0;
    v___x_4306_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___redArg(v_x_4303_, v_x_4304_, v_x_4305_);
    return v___x_4306_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___boxed(
    mut v_00_u03b2_4307_: *mut leanh::LeanObject,
    mut v_x_4308_: *mut leanh::LeanObject,
    mut v_x_4309_: *mut leanh::LeanObject,
    mut v_x_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5877__boxed_4311_: usize = 0;
    let mut v_res_4312_: u8 = 0;
    let mut v_r_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_5877__boxed_4311_ = leanh::lean_unbox_usize(v_x_4309_);
    leanh::lean_dec(v_x_4309_);
    v_res_4312_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_4307_, v_x_4308_, v_x_5877__boxed_4311_, v_x_4310_);
    leanh::lean_dec_ref(v_x_4310_);
    leanh::lean_dec_ref(v_x_4308_);
    v_r_4313_ = leanh::lean_box((v_res_4312_) as usize);
    return v_r_4313_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12(
    mut v_00_u03b2_4314_: *mut leanh::LeanObject,
    mut v_keys_4315_: *mut leanh::LeanObject,
    mut v_vals_4316_: *mut leanh::LeanObject,
    mut v_heq_4317_: *mut leanh::LeanObject,
    mut v_i_4318_: *mut leanh::LeanObject,
    mut v_k_4319_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4320_: u8 = 0;
    v___x_4320_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___redArg(v_keys_4315_, v_i_4318_, v_k_4319_);
    return v___x_4320_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___boxed(
    mut v_00_u03b2_4321_: *mut leanh::LeanObject,
    mut v_keys_4322_: *mut leanh::LeanObject,
    mut v_vals_4323_: *mut leanh::LeanObject,
    mut v_heq_4324_: *mut leanh::LeanObject,
    mut v_i_4325_: *mut leanh::LeanObject,
    mut v_k_4326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4327_: u8 = 0;
    let mut v_r_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12(v_00_u03b2_4321_, v_keys_4322_, v_vals_4323_, v_heq_4324_, v_i_4325_, v_k_4326_);
    leanh::lean_dec_ref(v_k_4326_);
    leanh::lean_dec_ref(v_vals_4323_);
    leanh::lean_dec_ref(v_keys_4322_);
    v_r_4328_ = leanh::lean_box((v_res_4327_) as usize);
    return v_r_4328_;
}
pub unsafe fn l_Lean_Compiler_CSimp_replaceConstant(
    mut v_env_4329_: *mut leanh::LeanObject,
    mut v_e_4330_: *mut leanh::LeanObject,
    mut v_a_4331_: *mut leanh::LeanObject,
    mut v_a_4332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4338_: u8 = 0;
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_a_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4350_: u8 = 0;
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4334_ = l_Lean_Compiler_CSimp_replaceConstant_x3f(
                    v_env_4329_,
                    v_e_4330_,
                    v_a_4331_,
                    v_a_4332_,
                );
                if leanh::lean_obj_tag(v___x_4334_) == 0 {
                    v_a_4335_ = leanh::lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4346_ = (!leanh::lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v___x_4337_ = v___x_4334_;
                        v_isShared_4338_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4335_);
                        leanh::lean_dec(v___x_4334_);
                        v___x_4337_ = leanh::lean_box(0);
                        v_isShared_4338_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4330_);
                    v_a_4347_ = leanh::lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4354_ = (!leanh::lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4354_ == 0 {
                        v___x_4349_ = v___x_4334_;
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4347_);
                        leanh::lean_dec(v___x_4334_);
                        v___x_4349_ = leanh::lean_box(0);
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4335_) == 0 {
                    if v_isShared_4338_ == 0 {
                        leanh::lean_ctor_set(v___x_4337_, 0, v_e_4330_);
                        v___x_4340_ = v___x_4337_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4341_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_e_4330_);
                        v___x_4340_ = v_reuseFailAlloc_4341_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4330_);
                    v_val_4342_ = leanh::lean_ctor_get(v_a_4335_, 0);
                    leanh::lean_inc(v_val_4342_);
                    leanh::lean_dec_ref_known(v_a_4335_, 1);
                    if v_isShared_4338_ == 0 {
                        leanh::lean_ctor_set(v___x_4337_, 0, v_val_4342_);
                        v___x_4344_ = v___x_4337_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4345_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_val_4342_);
                        v___x_4344_ = v_reuseFailAlloc_4345_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4340_;
            }
            3 => {
                return v___x_4344_;
            }
            4 => {
                if v_isShared_4350_ == 0 {
                    v___x_4352_ = v___x_4349_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
                    v___x_4352_ = v_reuseFailAlloc_4353_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_CSimp_replaceConstant___boxed(
    mut v_env_4355_: *mut leanh::LeanObject,
    mut v_e_4356_: *mut leanh::LeanObject,
    mut v_a_4357_: *mut leanh::LeanObject,
    mut v_a_4358_: *mut leanh::LeanObject,
    mut v_a_4359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4360_ =
        l_Lean_Compiler_CSimp_replaceConstant(v_env_4355_, v_e_4356_, v_a_4357_, v_a_4358_);
    leanh::lean_dec(v_a_4358_);
    leanh::lean_dec_ref(v_a_4357_);
    return v_res_4360_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_keys_4361_: *mut leanh::LeanObject,
    mut v_i_4362_: *mut leanh::LeanObject,
    mut v_k_4363_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: u8 = 0;
    let mut v_k_x27_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: u8 = 0;
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4364_ = lean_array_get_size(v_keys_4361_);
                v___x_4365_ = lean_nat_dec_lt(v_i_4362_, v___x_4364_);
                if v___x_4365_ == 0 {
                    leanh::lean_dec(v_i_4362_);
                    return v___x_4365_;
                } else {
                    v_k_x27_4366_ = lean_array_fget_borrowed(v_keys_4361_, v_i_4362_);
                    v___x_4367_ = lean_name_eq(v_k_4363_, v_k_x27_4366_);
                    if v___x_4367_ == 0 {
                        v___x_4368_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4369_ = lean_nat_add(v_i_4362_, v___x_4368_);
                        leanh::lean_dec(v_i_4362_);
                        v_i_4362_ = v___x_4369_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_4362_);
                        return v___x_4367_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_4371_: *mut leanh::LeanObject,
    mut v_i_4372_: *mut leanh::LeanObject,
    mut v_k_4373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4374_: u8 = 0;
    let mut v_r_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4374_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_4371_, v_i_4372_, v_k_4373_);
    leanh::lean_dec(v_k_4373_);
    leanh::lean_dec_ref(v_keys_4371_);
    v_r_4375_ = leanh::lean_box((v_res_4374_) as usize);
    return v_r_4375_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___redArg(
    mut v_x_4376_: *mut leanh::LeanObject,
    mut v_x_4377_: usize,
    mut v_x_4378_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: usize = 0;
    let mut v___x_4382_: usize = 0;
    let mut v___x_4383_: usize = 0;
    let mut v_j_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u8 = 0;
    let mut v_node_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: usize = 0;
    let mut v___x_4391_: u8 = 0;
    let mut v_ks_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4376_) == 0 {
                    v_es_4379_ = leanh::lean_ctor_get(v_x_4376_, 0);
                    v___x_4380_ = leanh::lean_box(2);
                    v___x_4381_ = 5usize;
                    v___x_4382_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4383_ = lean_usize_land(v_x_4377_, v___x_4382_);
                    v_j_4384_ = lean_usize_to_nat(v___x_4383_);
                    v___x_4385_ = lean_array_get_borrowed(v___x_4380_, v_es_4379_, v_j_4384_);
                    leanh::lean_dec(v_j_4384_);
                    match leanh::lean_obj_tag(v___x_4385_) {
                        0 => {
                            v_key_4386_ = leanh::lean_ctor_get(v___x_4385_, 0);
                            v___x_4387_ = lean_name_eq(v_x_4378_, v_key_4386_);
                            return v___x_4387_;
                        }
                        1 => {
                            v_node_4388_ = leanh::lean_ctor_get(v___x_4385_, 0);
                            v___x_4389_ = lean_usize_shift_right(v_x_4377_, v___x_4381_);
                            v_x_4376_ = v_node_4388_;
                            v_x_4377_ = v___x_4389_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4391_ = 0;
                            return v___x_4391_;
                        }
                    }
                } else {
                    v_ks_4392_ = leanh::lean_ctor_get(v_x_4376_, 0);
                    v___x_4393_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4394_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_4392_, v___x_4393_, v_x_4378_);
                    return v___x_4394_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_x_4395_: *mut leanh::LeanObject,
    mut v_x_4396_: *mut leanh::LeanObject,
    mut v_x_4397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_228__boxed_4398_: usize = 0;
    let mut v_res_4399_: u8 = 0;
    let mut v_r_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_228__boxed_4398_ = leanh::lean_unbox_usize(v_x_4396_);
    leanh::lean_dec(v_x_4396_);
    v_res_4399_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___redArg(v_x_4395_, v_x_228__boxed_4398_, v_x_4397_);
    leanh::lean_dec(v_x_4397_);
    leanh::lean_dec_ref(v_x_4395_);
    v_r_4400_ = leanh::lean_box((v_res_4399_) as usize);
    return v_r_4400_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___redArg(
    mut v_x_4401_: *mut leanh::LeanObject,
    mut v_x_4402_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_4404_: u64 = 0;
    let mut v___x_4405_: usize = 0;
    let mut v___x_4406_: u8 = 0;
    let mut v___x_4407_: u64 = 0;
    let mut v_hash_4408_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4402_) == 0 {
                    v___x_4407_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_4404_ = v___x_4407_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4408_ = leanh::lean_ctor_get_uint64(
                        v_x_4402_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4404_ = v_hash_4408_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4405_ = lean_uint64_to_usize(v___y_4404_);
                v___x_4406_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___redArg(v_x_4401_, v___x_4405_, v_x_4402_);
                return v___x_4406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___redArg___boxed(
    mut v_x_4409_: *mut leanh::LeanObject,
    mut v_x_4410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4411_: u8 = 0;
    let mut v_r_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4411_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___redArg(v_x_4409_, v_x_4410_);
    leanh::lean_dec(v_x_4410_);
    leanh::lean_dec_ref(v_x_4409_);
    v_r_4412_ = leanh::lean_box((v_res_4411_) as usize);
    return v_r_4412_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg(
    mut v_m_4413_: *mut leanh::LeanObject,
    mut v_a_4414_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4418_: u64 = 0;
    let mut v___x_4419_: u64 = 0;
    let mut v___x_4420_: u64 = 0;
    let mut v_fold_4421_: u64 = 0;
    let mut v___x_4422_: u64 = 0;
    let mut v___x_4423_: u64 = 0;
    let mut v___x_4424_: u64 = 0;
    let mut v___x_4425_: usize = 0;
    let mut v___x_4426_: usize = 0;
    let mut v___x_4427_: usize = 0;
    let mut v___x_4428_: usize = 0;
    let mut v___x_4429_: usize = 0;
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: u8 = 0;
    let mut v___x_4432_: u64 = 0;
    let mut v_hash_4433_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4415_ = leanh::lean_ctor_get(v_m_4413_, 1);
                v___x_4416_ = lean_array_get_size(v_buckets_4415_);
                if leanh::lean_obj_tag(v_a_4414_) == 0 {
                    v___x_4432_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_4418_ = v___x_4432_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4433_ = leanh::lean_ctor_get_uint64(
                        v_a_4414_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4418_ = v_hash_4433_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4419_ = 32u64;
                v___x_4420_ = lean_uint64_shift_right(v___y_4418_, v___x_4419_);
                v_fold_4421_ = lean_uint64_xor(v___y_4418_, v___x_4420_);
                v___x_4422_ = 16u64;
                v___x_4423_ = lean_uint64_shift_right(v_fold_4421_, v___x_4422_);
                v___x_4424_ = lean_uint64_xor(v_fold_4421_, v___x_4423_);
                v___x_4425_ = lean_uint64_to_usize(v___x_4424_);
                v___x_4426_ = lean_usize_of_nat(v___x_4416_);
                v___x_4427_ = 1usize;
                v___x_4428_ = lean_usize_sub(v___x_4426_, v___x_4427_);
                v___x_4429_ = lean_usize_land(v___x_4425_, v___x_4428_);
                v___x_4430_ = lean_array_uget_borrowed(v_buckets_4415_, v___x_4429_);
                v___x_4431_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_4414_, v___x_4430_);
                return v___x_4431_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg___boxed(
    mut v_m_4434_: *mut leanh::LeanObject,
    mut v_a_4435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4436_: u8 = 0;
    let mut v_r_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4436_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg(v_m_4434_, v_a_4435_);
    leanh::lean_dec(v_a_4435_);
    leanh::lean_dec_ref(v_m_4434_);
    v_r_4437_ = leanh::lean_box((v_res_4436_) as usize);
    return v_r_4437_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___redArg(
    mut v_x_4438_: *mut leanh::LeanObject,
    mut v_x_4439_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_stage_u2081_4440_: u8 = 0;
    v_stage_u2081_4440_ = leanh::lean_ctor_get_uint8(
        v_x_4438_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_4440_ == 0 {
        let mut v_map_u2081_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4443_: u8 = 0;
        v_map_u2081_4441_ = leanh::lean_ctor_get(v_x_4438_, 0);
        v_map_u2082_4442_ = leanh::lean_ctor_get(v_x_4438_, 1);
        v___x_4443_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg(v_map_u2081_4441_, v_x_4439_);
        if v___x_4443_ == 0 {
            let mut v___x_4444_: u8 = 0;
            v___x_4444_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___redArg(v_map_u2082_4442_, v_x_4439_);
            return v___x_4444_;
        } else {
            return v___x_4443_;
        }
    } else {
        let mut v_map_u2081_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4446_: u8 = 0;
        v_map_u2081_4445_ = leanh::lean_ctor_get(v_x_4438_, 0);
        v___x_4446_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg(v_map_u2081_4445_, v_x_4439_);
        return v___x_4446_;
    }
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___redArg___boxed(
    mut v_x_4447_: *mut leanh::LeanObject,
    mut v_x_4448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4449_: u8 = 0;
    let mut v_r_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4449_ = l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___redArg(
        v_x_4447_, v_x_4448_,
    );
    leanh::lean_dec(v_x_4448_);
    leanh::lean_dec_ref(v_x_4447_);
    v_r_4450_ = leanh::lean_box((v_res_4449_) as usize);
    return v_r_4450_;
}
pub unsafe fn l_Lean_Compiler_hasCSimpAttribute(
    mut v_env_4451_: *mut leanh::LeanObject,
    mut v_declName_4452_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_thmNames_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: u8 = 0;
    v___x_4453_ = l_Lean_Compiler_CSimp_ext;
    v_ext_4454_ = leanh::lean_ctor_get(v___x_4453_, 1);
    v_toEnvExtension_4455_ = leanh::lean_ctor_get(v_ext_4454_, 0);
    v_asyncMode_4456_ = leanh::lean_ctor_get(v_toEnvExtension_4455_, 2);
    v___x_4457_ = l_Lean_Compiler_CSimp_instInhabitedState_default;
    v___x_4458_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_4457_,
        v___x_4453_,
        v_env_4451_,
        v_asyncMode_4456_,
    );
    v_thmNames_4459_ = leanh::lean_ctor_get(v___x_4458_, 1);
    leanh::lean_inc_ref(v_thmNames_4459_);
    leanh::lean_dec(v___x_4458_);
    v___x_4460_ = l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___redArg(
        v_thmNames_4459_,
        v_declName_4452_,
    );
    leanh::lean_dec_ref(v_thmNames_4459_);
    return v___x_4460_;
}
pub unsafe fn l_Lean_Compiler_hasCSimpAttribute___boxed(
    mut v_env_4461_: *mut leanh::LeanObject,
    mut v_declName_4462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4463_: u8 = 0;
    let mut v_r_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4463_ = l_Lean_Compiler_hasCSimpAttribute(v_env_4461_, v_declName_4462_);
    leanh::lean_dec(v_declName_4462_);
    v_r_4464_ = leanh::lean_box((v_res_4463_) as usize);
    return v_r_4464_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0(
    mut v_00_u03b2_4465_: *mut leanh::LeanObject,
    mut v_x_4466_: *mut leanh::LeanObject,
    mut v_x_4467_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4468_: u8 = 0;
    v___x_4468_ = l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___redArg(
        v_x_4466_, v_x_4467_,
    );
    return v___x_4468_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___boxed(
    mut v_00_u03b2_4469_: *mut leanh::LeanObject,
    mut v_x_4470_: *mut leanh::LeanObject,
    mut v_x_4471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4472_: u8 = 0;
    let mut v_r_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4472_ = l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0(
        v_00_u03b2_4469_,
        v_x_4470_,
        v_x_4471_,
    );
    leanh::lean_dec(v_x_4471_);
    leanh::lean_dec_ref(v_x_4470_);
    v_r_4473_ = leanh::lean_box((v_res_4472_) as usize);
    return v_r_4473_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0(
    mut v_00_u03b2_4474_: *mut leanh::LeanObject,
    mut v_m_4475_: *mut leanh::LeanObject,
    mut v_a_4476_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4477_: u8 = 0;
    v___x_4477_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg(v_m_4475_, v_a_4476_);
    return v___x_4477_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___boxed(
    mut v_00_u03b2_4478_: *mut leanh::LeanObject,
    mut v_m_4479_: *mut leanh::LeanObject,
    mut v_a_4480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4481_: u8 = 0;
    let mut v_r_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4481_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0(v_00_u03b2_4478_, v_m_4479_, v_a_4480_);
    leanh::lean_dec(v_a_4480_);
    leanh::lean_dec_ref(v_m_4479_);
    v_r_4482_ = leanh::lean_box((v_res_4481_) as usize);
    return v_r_4482_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1(
    mut v_00_u03b2_4483_: *mut leanh::LeanObject,
    mut v_x_4484_: *mut leanh::LeanObject,
    mut v_x_4485_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4486_: u8 = 0;
    v___x_4486_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___redArg(v_x_4484_, v_x_4485_);
    return v___x_4486_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___boxed(
    mut v_00_u03b2_4487_: *mut leanh::LeanObject,
    mut v_x_4488_: *mut leanh::LeanObject,
    mut v_x_4489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4490_: u8 = 0;
    let mut v_r_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4490_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1(v_00_u03b2_4487_, v_x_4488_, v_x_4489_);
    leanh::lean_dec(v_x_4489_);
    leanh::lean_dec_ref(v_x_4488_);
    v_r_4491_ = leanh::lean_box((v_res_4490_) as usize);
    return v_r_4491_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4492_: *mut leanh::LeanObject,
    mut v_x_4493_: *mut leanh::LeanObject,
    mut v_x_4494_: usize,
    mut v_x_4495_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4496_: u8 = 0;
    v___x_4496_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___redArg(v_x_4493_, v_x_4494_, v_x_4495_);
    return v___x_4496_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_4497_: *mut leanh::LeanObject,
    mut v_x_4498_: *mut leanh::LeanObject,
    mut v_x_4499_: *mut leanh::LeanObject,
    mut v_x_4500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_374__boxed_4501_: usize = 0;
    let mut v_res_4502_: u8 = 0;
    let mut v_r_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_374__boxed_4501_ = leanh::lean_unbox_usize(v_x_4499_);
    leanh::lean_dec(v_x_4499_);
    v_res_4502_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2(v_00_u03b2_4497_, v_x_4498_, v_x_374__boxed_4501_, v_x_4500_);
    leanh::lean_dec(v_x_4500_);
    leanh::lean_dec_ref(v_x_4498_);
    v_r_4503_ = leanh::lean_box((v_res_4502_) as usize);
    return v_r_4503_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_4504_: *mut leanh::LeanObject,
    mut v_keys_4505_: *mut leanh::LeanObject,
    mut v_vals_4506_: *mut leanh::LeanObject,
    mut v_heq_4507_: *mut leanh::LeanObject,
    mut v_i_4508_: *mut leanh::LeanObject,
    mut v_k_4509_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4510_: u8 = 0;
    v___x_4510_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_4505_, v_i_4508_, v_k_4509_);
    return v___x_4510_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_4511_: *mut leanh::LeanObject,
    mut v_keys_4512_: *mut leanh::LeanObject,
    mut v_vals_4513_: *mut leanh::LeanObject,
    mut v_heq_4514_: *mut leanh::LeanObject,
    mut v_i_4515_: *mut leanh::LeanObject,
    mut v_k_4516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4517_: u8 = 0;
    let mut v_r_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4517_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_4511_, v_keys_4512_, v_vals_4513_, v_heq_4514_, v_i_4515_, v_k_4516_);
    leanh::lean_dec(v_k_4516_);
    leanh::lean_dec_ref(v_vals_4513_);
    leanh::lean_dec_ref(v_keys_4512_);
    v_r_4518_ = leanh::lean_box((v_res_4517_) as usize);
    return v_r_4518_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_CSimpAttr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Recognizers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Compiler_CSimp_instInhabitedState_default =
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default();
    leanh::lean_mark_persistent(l_Lean_Compiler_CSimp_instInhabitedState_default);
    l_Lean_Compiler_CSimp_instInhabitedState = _init_l_Lean_Compiler_CSimp_instInhabitedState();
    leanh::lean_mark_persistent(l_Lean_Compiler_CSimp_instInhabitedState);
    res = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_CSimp_ext = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Compiler_CSimp_ext);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_CSimpAttr(
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
pub unsafe fn initialize_Lean_Compiler_CSimpAttr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ScopedEnvExtension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_Recognizers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_CSimpAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_CSimpAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_CSimpAttr(builtin);
}
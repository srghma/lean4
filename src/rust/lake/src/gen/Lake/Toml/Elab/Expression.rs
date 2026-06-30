// Lean compiler output
// Module: Lake.Toml.Elab.Expression
// Imports: Lake.Toml.Elab.Value Lake.Toml.Grammar
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get, lean_array_get_size, lean_array_pop,
    lean_array_push, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_dec_eq,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_TSepArray_getElems___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_str___override, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_replaceRef,
};
use crate::r#gen::Lake::Toml::Data::Dict::{
    l_Lake_Toml_RBDict_appendArray___redArg, l_Lake_Toml_RBDict_empty,
    l_Lake_Toml_RBDict_findIdx_x3f___redArg, l_Lake_Toml_RBDict_push___redArg,
};
use crate::r#gen::Lake::Toml::Elab::Value::{
    initialize_Lake_Toml_Elab_Value, l_Lake_Toml_elabSimpleKey, l_Lake_Toml_elabVal,
    runtime_initialize_Lake_Toml_Elab_Value,
};
use crate::r#gen::Lake::Toml::Grammar::{
    initialize_Lake_Toml_Grammar, runtime_initialize_Lake_Toml_Grammar,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl,
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, l_Lean_Name_components,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_getRef, l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
pub static mut l_Lake_Toml_instInhabitedKeyTy_default: u8 = 0;
pub static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy: u8 = 0;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0_value:
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
    m_data: [118, 97, 108, 117, 101, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1_value:
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
    m_data: [116, 97, 98, 108, 101, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2_value:
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
    m_data: [97, 114, 114, 97, 121, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3_value:
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
    m_data: [100, 111, 116, 116, 101, 100, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value:
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
    m_data: [104, 101, 97, 100, 101, 114, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lake_Toml_instInhabitedElabState_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_Toml_instInhabitedElabState_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedElabState_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_instInhabitedElabState_default___closed__1_value:
    leanh::LeanCtorObject<6> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_instInhabitedElabState_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_Toml_instInhabitedElabState_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedElabState_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Toml_instInhabitedElabState_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedElabState_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedElabState_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 97, 110, 110, 111, 116, 32, 114, 101, 100, 101, 102, 105, 110, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [32, 107, 101, 121, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 111, 109, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 108, 101, 75, 101, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut leanh::LeanObject,16525079986463702690 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value) as *mut leanh::LeanObject,15900767148364346299 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value:
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
    m_data: [107, 101, 121, 118, 97, 108, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value
) as *mut leanh::LeanObject;
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut leanh::LeanObject,16525079986463702690 as *mut leanh::LeanObject] };
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value:
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
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value
        ) as *mut leanh::LeanObject,
        1860500813421358697 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 107, 101, 121, 45, 118, 97, 108, 117,
        101, 32, 112, 97, 105, 114, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value:
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
    m_data: [107, 101, 121, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value
) as *mut leanh::LeanObject;
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut leanh::LeanObject,16525079986463702690 as *mut leanh::LeanObject] };
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value:
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
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value
        ) as *mut leanh::LeanObject,
        3865642880800790572 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 107, 101, 121, 32, 115, 121, 110, 116,
        97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [40, 105, 110, 116, 101, 114, 110, 97, 108, 41, 32, 98, 97, 100, 32, 97, 114, 114, 97, 121, 32, 107, 101, 121, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_value:
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
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value:
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
    m_data: [115, 116, 100, 84, 97, 98, 108, 101, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value
) as *mut leanh::LeanObject;
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut leanh::LeanObject,16525079986463702690 as *mut leanh::LeanObject] };
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value:
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
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value
        ) as *mut leanh::LeanObject,
        14174431292734320076 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 116, 97, 98, 108, 101, 32, 115, 121,
        110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [97, 114, 114, 97, 121, 84, 97, 98, 108, 101, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value
) as *mut leanh::LeanObject;
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut leanh::LeanObject,16525079986463702690 as *mut leanh::LeanObject] };
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value) as *mut leanh::LeanObject,1392117589206424775 as *mut leanh::LeanObject] };
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 97, 114, 114, 97, 121, 32, 116, 97,
        98, 108, 101, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 101, 120, 112, 114, 101, 115, 115,
        105, 111, 110, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_elabToml___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 111, 109, 108, 0],
    };
static mut l_Lake_Toml_elabToml___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_elabToml___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static l_Lake_Toml_elabToml___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut leanh::LeanObject,16525079986463702690 as *mut leanh::LeanObject] };
pub static l_Lake_Toml_elabToml___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__0_value)
                as *mut leanh::LeanObject,
            4437657283425758961 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_elabToml___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_elabToml___closed__2_value: leanh::LeanStringObject<23> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 84, 79, 77, 76, 32, 115, 121, 110,
            116, 97, 120, 0,
        ],
    };
static mut l_Lake_Toml_elabToml___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_elabToml___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_elabToml___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Lake_Toml_elabToml___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut leanh::LeanObject,13012506173997729135 as *mut leanh::LeanObject] };
static l_Lake_Toml_elabToml___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut leanh::LeanObject,16525079986463702690 as *mut leanh::LeanObject] };
pub static l_Lake_Toml_elabToml___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value
            ) as *mut leanh::LeanObject,
            808944059858752425 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_elabToml___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__4_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx(
    mut v_x_1985_: u8,
) -> *mut leanh::LeanObject {
    match v_x_1985_ {
        0 => {
            let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1986_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1986_;
        }
        1 => {
            let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1987_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1987_;
        }
        2 => {
            let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1988_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1988_;
        }
        3 => {
            let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1989_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1989_;
        }
        _ => {
            let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1990_ = leanh::lean_unsigned_to_nat(4);
            return v___x_1990_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___boxed(
    mut v_x_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1992_: u8 = 0;
    let mut v_res_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1992_ = (leanh::lean_unbox(v_x_1991_) as u8);
    v_res_1993_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx(v_x_boxed_1992_);
    return v_res_1993_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx(
    mut v_x_1994_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1995_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx(v_x_1994_);
    return v___x_1995_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx___boxed(
    mut v_x_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_1997_: u8 = 0;
    let mut v_res_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1997_ = (leanh::lean_unbox(v_x_1996_) as u8);
    v_res_1998_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx(v_x_4__boxed_1997_);
    return v_res_1998_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(
    mut v_k_1999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1999_);
    return v_k_1999_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg___boxed(
    mut v_k_2000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2001_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(v_k_2000_);
    leanh::lean_dec(v_k_2000_);
    return v_res_2001_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(
    mut v_motive_2002_: *mut leanh::LeanObject,
    mut v_ctorIdx_2003_: *mut leanh::LeanObject,
    mut v_t_2004_: u8,
    mut v_h_2005_: *mut leanh::LeanObject,
    mut v_k_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2006_);
    return v_k_2006_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___boxed(
    mut v_motive_2007_: *mut leanh::LeanObject,
    mut v_ctorIdx_2008_: *mut leanh::LeanObject,
    mut v_t_2009_: *mut leanh::LeanObject,
    mut v_h_2010_: *mut leanh::LeanObject,
    mut v_k_2011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2012_: u8 = 0;
    let mut v_res_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2012_ = (leanh::lean_unbox(v_t_2009_) as u8);
    v_res_2013_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(
        v_motive_2007_,
        v_ctorIdx_2008_,
        v_t_boxed_2012_,
        v_h_2010_,
        v_k_2011_,
    );
    leanh::lean_dec(v_k_2011_);
    leanh::lean_dec(v_ctorIdx_2008_);
    return v_res_2013_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(
    mut v_value_2014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_value_2014_);
    return v_value_2014_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg___boxed(
    mut v_value_2015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2016_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(v_value_2015_);
    leanh::lean_dec(v_value_2015_);
    return v_res_2016_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(
    mut v_motive_2017_: *mut leanh::LeanObject,
    mut v_t_2018_: u8,
    mut v_h_2019_: *mut leanh::LeanObject,
    mut v_value_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_value_2020_);
    return v_value_2020_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___boxed(
    mut v_motive_2021_: *mut leanh::LeanObject,
    mut v_t_2022_: *mut leanh::LeanObject,
    mut v_h_2023_: *mut leanh::LeanObject,
    mut v_value_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2025_: u8 = 0;
    let mut v_res_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2025_ = (leanh::lean_unbox(v_t_2022_) as u8);
    v_res_2026_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(
        v_motive_2021_,
        v_t_boxed_2025_,
        v_h_2023_,
        v_value_2024_,
    );
    leanh::lean_dec(v_value_2024_);
    return v_res_2026_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(
    mut v_stdTable_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_stdTable_2027_);
    return v_stdTable_2027_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg___boxed(
    mut v_stdTable_2028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2029_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(
        v_stdTable_2028_,
    );
    leanh::lean_dec(v_stdTable_2028_);
    return v_res_2029_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(
    mut v_motive_2030_: *mut leanh::LeanObject,
    mut v_t_2031_: u8,
    mut v_h_2032_: *mut leanh::LeanObject,
    mut v_stdTable_2033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_stdTable_2033_);
    return v_stdTable_2033_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___boxed(
    mut v_motive_2034_: *mut leanh::LeanObject,
    mut v_t_2035_: *mut leanh::LeanObject,
    mut v_h_2036_: *mut leanh::LeanObject,
    mut v_stdTable_2037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2038_: u8 = 0;
    let mut v_res_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2038_ = (leanh::lean_unbox(v_t_2035_) as u8);
    v_res_2039_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(
        v_motive_2034_,
        v_t_boxed_2038_,
        v_h_2036_,
        v_stdTable_2037_,
    );
    leanh::lean_dec(v_stdTable_2037_);
    return v_res_2039_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(
    mut v_array_2040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_array_2040_);
    return v_array_2040_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg___boxed(
    mut v_array_2041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2042_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(v_array_2041_);
    leanh::lean_dec(v_array_2041_);
    return v_res_2042_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(
    mut v_motive_2043_: *mut leanh::LeanObject,
    mut v_t_2044_: u8,
    mut v_h_2045_: *mut leanh::LeanObject,
    mut v_array_2046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_array_2046_);
    return v_array_2046_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___boxed(
    mut v_motive_2047_: *mut leanh::LeanObject,
    mut v_t_2048_: *mut leanh::LeanObject,
    mut v_h_2049_: *mut leanh::LeanObject,
    mut v_array_2050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2051_: u8 = 0;
    let mut v_res_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2051_ = (leanh::lean_unbox(v_t_2048_) as u8);
    v_res_2052_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(
        v_motive_2047_,
        v_t_boxed_2051_,
        v_h_2049_,
        v_array_2050_,
    );
    leanh::lean_dec(v_array_2050_);
    return v_res_2052_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(
    mut v_dottedPrefix_2053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_dottedPrefix_2053_);
    return v_dottedPrefix_2053_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg___boxed(
    mut v_dottedPrefix_2054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2055_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(
            v_dottedPrefix_2054_,
        );
    leanh::lean_dec(v_dottedPrefix_2054_);
    return v_res_2055_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(
    mut v_motive_2056_: *mut leanh::LeanObject,
    mut v_t_2057_: u8,
    mut v_h_2058_: *mut leanh::LeanObject,
    mut v_dottedPrefix_2059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_dottedPrefix_2059_);
    return v_dottedPrefix_2059_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___boxed(
    mut v_motive_2060_: *mut leanh::LeanObject,
    mut v_t_2061_: *mut leanh::LeanObject,
    mut v_h_2062_: *mut leanh::LeanObject,
    mut v_dottedPrefix_2063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2064_: u8 = 0;
    let mut v_res_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2064_ = (leanh::lean_unbox(v_t_2061_) as u8);
    v_res_2065_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(
        v_motive_2060_,
        v_t_boxed_2064_,
        v_h_2062_,
        v_dottedPrefix_2063_,
    );
    leanh::lean_dec(v_dottedPrefix_2063_);
    return v_res_2065_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(
    mut v_headerPrefix_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_headerPrefix_2066_);
    return v_headerPrefix_2066_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg___boxed(
    mut v_headerPrefix_2067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2068_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(
            v_headerPrefix_2067_,
        );
    leanh::lean_dec(v_headerPrefix_2067_);
    return v_res_2068_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(
    mut v_motive_2069_: *mut leanh::LeanObject,
    mut v_t_2070_: u8,
    mut v_h_2071_: *mut leanh::LeanObject,
    mut v_headerPrefix_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_headerPrefix_2072_);
    return v_headerPrefix_2072_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___boxed(
    mut v_motive_2073_: *mut leanh::LeanObject,
    mut v_t_2074_: *mut leanh::LeanObject,
    mut v_h_2075_: *mut leanh::LeanObject,
    mut v_headerPrefix_2076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2077_: u8 = 0;
    let mut v_res_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2077_ = (leanh::lean_unbox(v_t_2074_) as u8);
    v_res_2078_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(
        v_motive_2073_,
        v_t_boxed_2077_,
        v_h_2075_,
        v_headerPrefix_2076_,
    );
    leanh::lean_dec(v_headerPrefix_2076_);
    return v_res_2078_;
}
pub unsafe fn _init_l_Lake_Toml_instInhabitedKeyTy_default() -> u8 {
    let mut v___x_2079_: u8 = 0;
    v___x_2079_ = 0;
    return v___x_2079_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy() -> u8 {
    let mut v___x_2080_: u8 = 0;
    v___x_2080_ = 0;
    return v___x_2080_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(
    mut v_ty_2086_: u8,
) -> *mut leanh::LeanObject {
    match v_ty_2086_ {
        0 => {
            let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2087_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0;
            return v___x_2087_;
        }
        1 => {
            let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2088_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1;
            return v___x_2088_;
        }
        2 => {
            let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2089_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2;
            return v___x_2089_;
        }
        3 => {
            let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2090_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3;
            return v___x_2090_;
        }
        _ => {
            let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2091_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4;
            return v___x_2091_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed(
    mut v_ty_2092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ty_boxed_2093_: u8 = 0;
    let mut v_res_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ty_boxed_2093_ = (leanh::lean_unbox(v_ty_2092_) as u8);
    v_res_2094_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v_ty_boxed_2093_);
    return v_res_2094_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(
    mut v_ty_2097_: u8,
) -> u8 {
    match v_ty_2097_ {
        1 => {
            let mut v___x_2098_: u8 = 0;
            v___x_2098_ = 1;
            return v___x_2098_;
        }
        4 => {
            let mut v___x_2099_: u8 = 0;
            v___x_2099_ = 1;
            return v___x_2099_;
        }
        3 => {
            let mut v___x_2100_: u8 = 0;
            v___x_2100_ = 1;
            return v___x_2100_;
        }
        _ => {
            let mut v___x_2101_: u8 = 0;
            v___x_2101_ = 0;
            return v___x_2101_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix___boxed(
    mut v_ty_2102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ty_boxed_2103_: u8 = 0;
    let mut v_res_2104_: u8 = 0;
    let mut v_r_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ty_boxed_2103_ = (leanh::lean_unbox(v_ty_2102_) as u8);
    v_res_2104_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(v_ty_boxed_2103_);
    v_r_2105_ = leanh::lean_box((v_res_2104_) as usize);
    return v_r_2105_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2114_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2115_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0);
    v___x_2116_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2116_, 0, v___x_2115_);
    return v___x_2116_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
    v___x_2118_ = leanh::lean_unsigned_to_nat(0);
    v___x_2119_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2119_, 0, v___x_2118_);
    leanh::lean_ctor_set(v___x_2119_, 1, v___x_2118_);
    leanh::lean_ctor_set(v___x_2119_, 2, v___x_2118_);
    leanh::lean_ctor_set(v___x_2119_, 3, v___x_2118_);
    leanh::lean_ctor_set(v___x_2119_, 4, v___x_2117_);
    leanh::lean_ctor_set(v___x_2119_, 5, v___x_2117_);
    leanh::lean_ctor_set(v___x_2119_, 6, v___x_2117_);
    leanh::lean_ctor_set(v___x_2119_, 7, v___x_2117_);
    leanh::lean_ctor_set(v___x_2119_, 8, v___x_2117_);
    leanh::lean_ctor_set(v___x_2119_, 9, v___x_2117_);
    return v___x_2119_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = leanh::lean_unsigned_to_nat(32);
    v___x_2121_ = lean_mk_empty_array_with_capacity(v___x_2120_);
    v___x_2122_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2122_, 0, v___x_2121_);
    return v___x_2122_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2123_: usize = 0;
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2123_ = 5usize;
    v___x_2124_ = leanh::lean_unsigned_to_nat(0);
    v___x_2125_ = leanh::lean_unsigned_to_nat(32);
    v___x_2126_ = lean_mk_empty_array_with_capacity(v___x_2125_);
    v___x_2127_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3);
    v___x_2128_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2128_, 0, v___x_2127_);
    leanh::lean_ctor_set(v___x_2128_, 1, v___x_2126_);
    leanh::lean_ctor_set(v___x_2128_, 2, v___x_2124_);
    leanh::lean_ctor_set(v___x_2128_, 3, v___x_2124_);
    leanh::lean_ctor_set_usize(v___x_2128_, 4, v___x_2123_);
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2129_ = leanh::lean_box(1);
    v___x_2130_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4);
    v___x_2131_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
    v___x_2132_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
    leanh::lean_ctor_set(v___x_2132_, 1, v___x_2130_);
    leanh::lean_ctor_set(v___x_2132_, 2, v___x_2129_);
    return v___x_2132_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(
    mut v_msgData_2133_: *mut leanh::LeanObject,
    mut v___y_2134_: *mut leanh::LeanObject,
    mut v___y_2135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = lean_st_ref_get(v___y_2135_);
    v_env_2138_ = leanh::lean_ctor_get(v___x_2137_, 0);
    leanh::lean_inc_ref(v_env_2138_);
    leanh::lean_dec(v___x_2137_);
    v_options_2139_ = leanh::lean_ctor_get(v___y_2134_, 2);
    v___x_2140_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2);
    v___x_2141_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5);
    leanh::lean_inc_ref(v_options_2139_);
    v___x_2142_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2142_, 0, v_env_2138_);
    leanh::lean_ctor_set(v___x_2142_, 1, v___x_2140_);
    leanh::lean_ctor_set(v___x_2142_, 2, v___x_2141_);
    leanh::lean_ctor_set(v___x_2142_, 3, v_options_2139_);
    v___x_2143_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2143_, 0, v___x_2142_);
    leanh::lean_ctor_set(v___x_2143_, 1, v_msgData_2133_);
    v___x_2144_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2144_, 0, v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_2145_: *mut leanh::LeanObject,
    mut v___y_2146_: *mut leanh::LeanObject,
    mut v___y_2147_: *mut leanh::LeanObject,
    mut v___y_2148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2149_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msgData_2145_, v___y_2146_, v___y_2147_);
    leanh::lean_dec(v___y_2147_);
    leanh::lean_dec_ref(v___y_2146_);
    return v_res_2149_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(
    mut v_msg_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2159_: u8 = 0;
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2154_ = leanh::lean_ctor_get(v___y_2151_, 5);
                v___x_2155_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_2150_, v___y_2151_, v___y_2152_);
                v_a_2156_ = leanh::lean_ctor_get(v___x_2155_, 0);
                v_isSharedCheck_2164_ = (!leanh::lean_is_exclusive(v___x_2155_)) as u8;
                if v_isSharedCheck_2164_ == 0 {
                    v___x_2158_ = v___x_2155_;
                    v_isShared_2159_ = v_isSharedCheck_2164_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2156_);
                    leanh::lean_dec(v___x_2155_);
                    v___x_2158_ = leanh::lean_box(0);
                    v_isShared_2159_ = v_isSharedCheck_2164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2154_);
                v___x_2160_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2160_, 0, v_ref_2154_);
                leanh::lean_ctor_set(v___x_2160_, 1, v_a_2156_);
                if v_isShared_2159_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2158_, 1);
                    leanh::lean_ctor_set(v___x_2158_, 0, v___x_2160_);
                    v___x_2162_ = v___x_2158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
                    v___x_2162_ = v_reuseFailAlloc_2163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg___boxed(
    mut v_msg_2165_: *mut leanh::LeanObject,
    mut v___y_2166_: *mut leanh::LeanObject,
    mut v___y_2167_: *mut leanh::LeanObject,
    mut v___y_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_2165_, v___y_2166_, v___y_2167_);
    leanh::lean_dec(v___y_2167_);
    leanh::lean_dec_ref(v___y_2166_);
    return v_res_2169_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(
    mut v_ref_2170_: *mut leanh::LeanObject,
    mut v_msg_2171_: *mut leanh::LeanObject,
    mut v___y_2172_: *mut leanh::LeanObject,
    mut v___y_2173_: *mut leanh::LeanObject,
    mut v___y_2174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2188_: u8 = 0;
    let mut v_cancelTk_x3f_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2190_: u8 = 0;
    let mut v_inheritedTraceOptions_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2176_ = leanh::lean_ctor_get(v___y_2173_, 0);
    v_fileMap_2177_ = leanh::lean_ctor_get(v___y_2173_, 1);
    v_options_2178_ = leanh::lean_ctor_get(v___y_2173_, 2);
    v_currRecDepth_2179_ = leanh::lean_ctor_get(v___y_2173_, 3);
    v_maxRecDepth_2180_ = leanh::lean_ctor_get(v___y_2173_, 4);
    v_ref_2181_ = leanh::lean_ctor_get(v___y_2173_, 5);
    v_currNamespace_2182_ = leanh::lean_ctor_get(v___y_2173_, 6);
    v_openDecls_2183_ = leanh::lean_ctor_get(v___y_2173_, 7);
    v_initHeartbeats_2184_ = leanh::lean_ctor_get(v___y_2173_, 8);
    v_maxHeartbeats_2185_ = leanh::lean_ctor_get(v___y_2173_, 9);
    v_quotContext_2186_ = leanh::lean_ctor_get(v___y_2173_, 10);
    v_currMacroScope_2187_ = leanh::lean_ctor_get(v___y_2173_, 11);
    v_diag_2188_ = leanh::lean_ctor_get_uint8(
        v___y_2173_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2189_ = leanh::lean_ctor_get(v___y_2173_, 12);
    v_suppressElabErrors_2190_ = leanh::lean_ctor_get_uint8(
        v___y_2173_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2191_ = leanh::lean_ctor_get(v___y_2173_, 13);
    v_ref_2192_ = l_Lean_replaceRef(v_ref_2170_, v_ref_2181_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_2191_);
    leanh::lean_inc(v_cancelTk_x3f_2189_);
    leanh::lean_inc(v_currMacroScope_2187_);
    leanh::lean_inc(v_quotContext_2186_);
    leanh::lean_inc(v_maxHeartbeats_2185_);
    leanh::lean_inc(v_initHeartbeats_2184_);
    leanh::lean_inc(v_openDecls_2183_);
    leanh::lean_inc(v_currNamespace_2182_);
    leanh::lean_inc(v_maxRecDepth_2180_);
    leanh::lean_inc(v_currRecDepth_2179_);
    leanh::lean_inc_ref(v_options_2178_);
    leanh::lean_inc_ref(v_fileMap_2177_);
    leanh::lean_inc_ref(v_fileName_2176_);
    v___x_2193_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_2193_, 0, v_fileName_2176_);
    leanh::lean_ctor_set(v___x_2193_, 1, v_fileMap_2177_);
    leanh::lean_ctor_set(v___x_2193_, 2, v_options_2178_);
    leanh::lean_ctor_set(v___x_2193_, 3, v_currRecDepth_2179_);
    leanh::lean_ctor_set(v___x_2193_, 4, v_maxRecDepth_2180_);
    leanh::lean_ctor_set(v___x_2193_, 5, v_ref_2192_);
    leanh::lean_ctor_set(v___x_2193_, 6, v_currNamespace_2182_);
    leanh::lean_ctor_set(v___x_2193_, 7, v_openDecls_2183_);
    leanh::lean_ctor_set(v___x_2193_, 8, v_initHeartbeats_2184_);
    leanh::lean_ctor_set(v___x_2193_, 9, v_maxHeartbeats_2185_);
    leanh::lean_ctor_set(v___x_2193_, 10, v_quotContext_2186_);
    leanh::lean_ctor_set(v___x_2193_, 11, v_currMacroScope_2187_);
    leanh::lean_ctor_set(v___x_2193_, 12, v_cancelTk_x3f_2189_);
    leanh::lean_ctor_set(v___x_2193_, 13, v_inheritedTraceOptions_2191_);
    leanh::lean_ctor_set_uint8(
        v___x_2193_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_2188_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2193_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2190_,
    );
    v___x_2194_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_2171_, v___x_2193_, v___y_2174_);
    leanh::lean_dec_ref_known(v___x_2193_, 14);
    return v___x_2194_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(
    mut v_ref_2195_: *mut leanh::LeanObject,
    mut v_msg_2196_: *mut leanh::LeanObject,
    mut v___y_2197_: *mut leanh::LeanObject,
    mut v___y_2198_: *mut leanh::LeanObject,
    mut v___y_2199_: *mut leanh::LeanObject,
    mut v___y_2200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_2195_, v_msg_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
    leanh::lean_dec(v___y_2199_);
    leanh::lean_dec_ref(v___y_2198_);
    leanh::lean_dec_ref(v___y_2197_);
    leanh::lean_dec(v_ref_2195_);
    return v_res_2201_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0;
    v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
    return v___x_2204_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2;
    v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
    return v___x_2207_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4;
    v___x_2210_ = l_Lean_stringToMessageData(v___x_2209_);
    return v___x_2210_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(
    mut v_as_2211_: *mut leanh::LeanObject,
    mut v_i_2212_: usize,
    mut v_stop_2213_: usize,
    mut v_b_2214_: *mut leanh::LeanObject,
    mut v___y_2215_: *mut leanh::LeanObject,
    mut v___y_2216_: *mut leanh::LeanObject,
    mut v___y_2217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: usize = 0;
    let mut v___x_2223_: usize = 0;
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyTys_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currKey_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2261_: u8 = 0;
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2265_: u8 = 0;
    let mut v_reuseFailAlloc_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2267_: u8 = 0;
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut v_unused_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2287_: u8 = 0;
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2291_: u8 = 0;
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2225_ = lean_usize_dec_eq(v_i_2212_, v_stop_2213_);
                if v___x_2225_ == 0 {
                    v___x_2226_ = lean_array_uget_borrowed(v_as_2211_, v_i_2212_);
                    leanh::lean_inc(v___x_2226_);
                    v___x_2227_ = l_Lake_Toml_elabSimpleKey(v___x_2226_, v___y_2216_, v___y_2217_);
                    if leanh::lean_obj_tag(v___x_2227_) == 0 {
                        v_a_2228_ = leanh::lean_ctor_get(v___x_2227_, 0);
                        leanh::lean_inc(v_a_2228_);
                        leanh::lean_dec_ref_known(v___x_2227_, 1);
                        v_keyTys_2229_ = leanh::lean_ctor_get(v___y_2215_, 0);
                        v_arrKeyTys_2230_ = leanh::lean_ctor_get(v___y_2215_, 1);
                        v_arrParents_2231_ = leanh::lean_ctor_get(v___y_2215_, 2);
                        v_currArrKey_2232_ = leanh::lean_ctor_get(v___y_2215_, 3);
                        v_currKey_2233_ = leanh::lean_ctor_get(v___y_2215_, 4);
                        v_items_2234_ = leanh::lean_ctor_get(v___y_2215_, 5);
                        v___x_2235_ = l_Lean_Name_str___override(v_b_2214_, v_a_2228_);
                        v___x_2236_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_2229_, v___x_2235_);
                        if leanh::lean_obj_tag(v___x_2236_) == 1 {
                            v_val_2237_ = leanh::lean_ctor_get(v___x_2236_, 0);
                            v_isSharedCheck_2267_ =
                                (!leanh::lean_is_exclusive(v___x_2236_)) as u8;
                            if v_isSharedCheck_2267_ == 0 {
                                v___x_2239_ = v___x_2236_;
                                v_isShared_2240_ = v_isSharedCheck_2267_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_2237_);
                                leanh::lean_dec(v___x_2236_);
                                v___x_2239_ = leanh::lean_box(0);
                                v_isShared_2240_ = v_isSharedCheck_2267_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_inc_ref(v_items_2234_);
                            leanh::lean_inc(v_currKey_2233_);
                            leanh::lean_inc(v_currArrKey_2232_);
                            leanh::lean_inc(v_arrParents_2231_);
                            leanh::lean_inc(v_arrKeyTys_2230_);
                            leanh::lean_inc(v_keyTys_2229_);
                            leanh::lean_dec(v___x_2236_);
                            v_isSharedCheck_2277_ =
                                (!leanh::lean_is_exclusive(v___y_2215_)) as u8;
                            if v_isSharedCheck_2277_ == 0 {
                                v_unused_2278_ = leanh::lean_ctor_get(v___y_2215_, 5);
                                leanh::lean_dec(v_unused_2278_);
                                v_unused_2279_ = leanh::lean_ctor_get(v___y_2215_, 4);
                                leanh::lean_dec(v_unused_2279_);
                                v_unused_2280_ = leanh::lean_ctor_get(v___y_2215_, 3);
                                leanh::lean_dec(v_unused_2280_);
                                v_unused_2281_ = leanh::lean_ctor_get(v___y_2215_, 2);
                                leanh::lean_dec(v_unused_2281_);
                                v_unused_2282_ = leanh::lean_ctor_get(v___y_2215_, 1);
                                leanh::lean_dec(v_unused_2282_);
                                v_unused_2283_ = leanh::lean_ctor_get(v___y_2215_, 0);
                                leanh::lean_dec(v_unused_2283_);
                                v___x_2269_ = v___y_2215_;
                                v_isShared_2270_ = v_isSharedCheck_2277_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_dec(v___y_2215_);
                                v___x_2269_ = leanh::lean_box(0);
                                v_isShared_2270_ = v_isSharedCheck_2277_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_2215_);
                        leanh::lean_dec(v_b_2214_);
                        v_a_2284_ = leanh::lean_ctor_get(v___x_2227_, 0);
                        v_isSharedCheck_2291_ =
                            (!leanh::lean_is_exclusive(v___x_2227_)) as u8;
                        if v_isSharedCheck_2291_ == 0 {
                            v___x_2286_ = v___x_2227_;
                            v_isShared_2287_ = v_isSharedCheck_2291_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2284_);
                            leanh::lean_dec(v___x_2227_);
                            v___x_2286_ = leanh::lean_box(0);
                            v_isShared_2287_ = v_isSharedCheck_2291_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_2292_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2292_, 0, v_b_2214_);
                    leanh::lean_ctor_set(v___x_2292_, 1, v___y_2215_);
                    v___x_2293_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2293_, 0, v___x_2292_);
                    return v___x_2293_;
                }
            }
            1 => {
                v___x_2222_ = 1usize;
                v___x_2223_ = lean_usize_add(v_i_2212_, v___x_2222_);
                v_i_2212_ = v___x_2223_;
                v_b_2214_ = v_fst_2220_;
                v___y_2215_ = v_snd_2221_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2241_ = (leanh::lean_unbox(v_val_2237_) as u8);
                if v___x_2241_ == 3 {
                    leanh::lean_del_object(v___x_2239_);
                    leanh::lean_dec(v_val_2237_);
                    v_fst_2220_ = v___x_2235_;
                    v_snd_2221_ = v___y_2215_;
                    state = 1;
                    continue;
                } else {
                    v___x_2242_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
                    v___x_2243_ = (leanh::lean_unbox(v_val_2237_) as u8);
                    leanh::lean_dec(v_val_2237_);
                    v___x_2244_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(
                        v___x_2243_,
                    );
                    if v_isShared_2240_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2239_, 3);
                        leanh::lean_ctor_set(v___x_2239_, 0, v___x_2244_);
                        v___x_2246_ = v___x_2239_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2266_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2244_);
                        v___x_2246_ = v_reuseFailAlloc_2266_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2247_ = l_Lean_MessageData_ofFormat(v___x_2246_);
                v___x_2248_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2248_, 0, v___x_2242_);
                leanh::lean_ctor_set(v___x_2248_, 1, v___x_2247_);
                v___x_2249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
                v___x_2250_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2250_, 0, v___x_2248_);
                leanh::lean_ctor_set(v___x_2250_, 1, v___x_2249_);
                leanh::lean_inc(v___x_2235_);
                v___x_2251_ = l_Lean_MessageData_ofName(v___x_2235_);
                v___x_2252_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2252_, 0, v___x_2250_);
                leanh::lean_ctor_set(v___x_2252_, 1, v___x_2251_);
                v___x_2253_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                v___x_2254_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2254_, 0, v___x_2252_);
                leanh::lean_ctor_set(v___x_2254_, 1, v___x_2253_);
                v___x_2255_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2226_, v___x_2254_, v___y_2215_, v___y_2216_, v___y_2217_);
                leanh::lean_dec_ref(v___y_2215_);
                if leanh::lean_obj_tag(v___x_2255_) == 0 {
                    v_a_2256_ = leanh::lean_ctor_get(v___x_2255_, 0);
                    leanh::lean_inc(v_a_2256_);
                    leanh::lean_dec_ref_known(v___x_2255_, 1);
                    v_snd_2257_ = leanh::lean_ctor_get(v_a_2256_, 1);
                    leanh::lean_inc(v_snd_2257_);
                    leanh::lean_dec(v_a_2256_);
                    v_fst_2220_ = v___x_2235_;
                    v_snd_2221_ = v_snd_2257_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2235_);
                    v_a_2258_ = leanh::lean_ctor_get(v___x_2255_, 0);
                    v_isSharedCheck_2265_ = (!leanh::lean_is_exclusive(v___x_2255_)) as u8;
                    if v_isSharedCheck_2265_ == 0 {
                        v___x_2260_ = v___x_2255_;
                        v_isShared_2261_ = v_isSharedCheck_2265_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2258_);
                        leanh::lean_dec(v___x_2255_);
                        v___x_2260_ = leanh::lean_box(0);
                        v_isShared_2261_ = v_isSharedCheck_2265_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2261_ == 0 {
                    v___x_2263_ = v___x_2260_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2264_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
                    v___x_2263_ = v_reuseFailAlloc_2264_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2263_;
            }
            6 => {
                v___x_2271_ = 3;
                v___x_2272_ = leanh::lean_box((v___x_2271_) as usize);
                leanh::lean_inc(v___x_2235_);
                v___x_2273_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2235_, v___x_2272_, v_keyTys_2229_);
                if v_isShared_2270_ == 0 {
                    leanh::lean_ctor_set(v___x_2269_, 0, v___x_2273_);
                    v___x_2275_ = v___x_2269_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2276_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_arrKeyTys_2230_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 2, v_arrParents_2231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 3, v_currArrKey_2232_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 4, v_currKey_2233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 5, v_items_2234_);
                    v___x_2275_ = v_reuseFailAlloc_2276_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_2220_ = v___x_2235_;
                v_snd_2221_ = v___x_2275_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_2287_ == 0 {
                    v___x_2289_ = v___x_2286_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2290_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
                    v___x_2289_ = v_reuseFailAlloc_2290_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(
    mut v_as_2294_: *mut leanh::LeanObject,
    mut v_i_2295_: *mut leanh::LeanObject,
    mut v_stop_2296_: *mut leanh::LeanObject,
    mut v_b_2297_: *mut leanh::LeanObject,
    mut v___y_2298_: *mut leanh::LeanObject,
    mut v___y_2299_: *mut leanh::LeanObject,
    mut v___y_2300_: *mut leanh::LeanObject,
    mut v___y_2301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2302_: usize = 0;
    let mut v_stop_boxed_2303_: usize = 0;
    let mut v_res_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2302_ = leanh::lean_unbox_usize(v_i_2295_);
    leanh::lean_dec(v_i_2295_);
    v_stop_boxed_2303_ = leanh::lean_unbox_usize(v_stop_2296_);
    leanh::lean_dec(v_stop_2296_);
    v_res_2304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_2294_, v_i_boxed_2302_, v_stop_boxed_2303_, v_b_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
    leanh::lean_dec(v___y_2300_);
    leanh::lean_dec_ref(v___y_2299_);
    leanh::lean_dec_ref(v_as_2294_);
    return v_res_2304_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(
    mut v_ks_2305_: *mut leanh::LeanObject,
    mut v_a_2306_: *mut leanh::LeanObject,
    mut v_a_2307_: *mut leanh::LeanObject,
    mut v_a_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_currKey_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u8 = 0;
    v_currKey_2310_ = leanh::lean_ctor_get(v_a_2306_, 4);
    leanh::lean_inc(v_currKey_2310_);
    v___x_2311_ = leanh::lean_unsigned_to_nat(0);
    v___x_2312_ = lean_array_get_size(v_ks_2305_);
    v___x_2313_ = lean_nat_dec_lt(v___x_2311_, v___x_2312_);
    if v___x_2313_ == 0 {
        let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2314_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2314_, 0, v_currKey_2310_);
        leanh::lean_ctor_set(v___x_2314_, 1, v_a_2306_);
        v___x_2315_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2315_, 0, v___x_2314_);
        return v___x_2315_;
    } else {
        let mut v___x_2316_: u8 = 0;
        v___x_2316_ = lean_nat_dec_le(v___x_2312_, v___x_2312_);
        if v___x_2316_ == 0 {
            if v___x_2313_ == 0 {
                let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2317_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2317_, 0, v_currKey_2310_);
                leanh::lean_ctor_set(v___x_2317_, 1, v_a_2306_);
                v___x_2318_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2318_, 0, v___x_2317_);
                return v___x_2318_;
            } else {
                let mut v___x_2319_: usize = 0;
                let mut v___x_2320_: usize = 0;
                let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2319_ = 0usize;
                v___x_2320_ = lean_usize_of_nat(v___x_2312_);
                v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_2305_, v___x_2319_, v___x_2320_, v_currKey_2310_, v_a_2306_, v_a_2307_, v_a_2308_);
                return v___x_2321_;
            }
        } else {
            let mut v___x_2322_: usize = 0;
            let mut v___x_2323_: usize = 0;
            let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2322_ = 0usize;
            v___x_2323_ = lean_usize_of_nat(v___x_2312_);
            v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_2305_, v___x_2322_, v___x_2323_, v_currKey_2310_, v_a_2306_, v_a_2307_, v_a_2308_);
            return v___x_2324_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(
    mut v_ks_2325_: *mut leanh::LeanObject,
    mut v_a_2326_: *mut leanh::LeanObject,
    mut v_a_2327_: *mut leanh::LeanObject,
    mut v_a_2328_: *mut leanh::LeanObject,
    mut v_a_2329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2330_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(
        v_ks_2325_, v_a_2326_, v_a_2327_, v_a_2328_,
    );
    leanh::lean_dec(v_a_2328_);
    leanh::lean_dec_ref(v_a_2327_);
    leanh::lean_dec_ref(v_ks_2325_);
    return v_res_2330_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(
    mut v_00_u03b1_2331_: *mut leanh::LeanObject,
    mut v_ref_2332_: *mut leanh::LeanObject,
    mut v_msg_2333_: *mut leanh::LeanObject,
    mut v___y_2334_: *mut leanh::LeanObject,
    mut v___y_2335_: *mut leanh::LeanObject,
    mut v___y_2336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_2332_, v_msg_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
    return v___x_2338_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(
    mut v_00_u03b1_2339_: *mut leanh::LeanObject,
    mut v_ref_2340_: *mut leanh::LeanObject,
    mut v_msg_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2346_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_2339_, v_ref_2340_, v_msg_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
    leanh::lean_dec(v___y_2344_);
    leanh::lean_dec_ref(v___y_2343_);
    leanh::lean_dec_ref(v___y_2342_);
    leanh::lean_dec(v_ref_2340_);
    return v_res_2346_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(
    mut v_00_u03b1_2347_: *mut leanh::LeanObject,
    mut v_msg_2348_: *mut leanh::LeanObject,
    mut v___y_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_2348_, v___y_2350_, v___y_2351_);
    return v___x_2353_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(
    mut v_00_u03b1_2354_: *mut leanh::LeanObject,
    mut v_msg_2355_: *mut leanh::LeanObject,
    mut v___y_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
    mut v___y_2358_: *mut leanh::LeanObject,
    mut v___y_2359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2360_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_2354_, v_msg_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
    leanh::lean_dec(v___y_2358_);
    leanh::lean_dec_ref(v___y_2357_);
    leanh::lean_dec_ref(v___y_2356_);
    return v_res_2360_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(
    mut v___x_2361_: u8,
    mut v_as_2362_: *mut leanh::LeanObject,
    mut v_i_2363_: usize,
    mut v_stop_2364_: usize,
    mut v_b_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: usize = 0;
    let mut v___x_2369_: usize = 0;
    let mut v___x_2371_: u8 = 0;
    let mut v_fst_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u8 = 0;
    let mut v_snd_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2382_: u8 = 0;
    let mut v_unused_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2387_: u8 = 0;
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v_unused_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2371_ = lean_usize_dec_eq(v_i_2363_, v_stop_2364_);
                if v___x_2371_ == 0 {
                    v_fst_2372_ = leanh::lean_ctor_get(v_b_2365_, 0);
                    v___x_2373_ = (leanh::lean_unbox(v_fst_2372_) as u8);
                    if v___x_2373_ == 0 {
                        v_snd_2374_ = leanh::lean_ctor_get(v_b_2365_, 1);
                        v_isSharedCheck_2382_ = (!leanh::lean_is_exclusive(v_b_2365_)) as u8;
                        if v_isSharedCheck_2382_ == 0 {
                            v_unused_2383_ = leanh::lean_ctor_get(v_b_2365_, 0);
                            leanh::lean_dec(v_unused_2383_);
                            v___x_2376_ = v_b_2365_;
                            v_isShared_2377_ = v_isSharedCheck_2382_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_2374_);
                            leanh::lean_dec(v_b_2365_);
                            v___x_2376_ = leanh::lean_box(0);
                            v_isShared_2377_ = v_isSharedCheck_2382_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_2384_ = leanh::lean_ctor_get(v_b_2365_, 1);
                        v_isSharedCheck_2394_ = (!leanh::lean_is_exclusive(v_b_2365_)) as u8;
                        if v_isSharedCheck_2394_ == 0 {
                            v_unused_2395_ = leanh::lean_ctor_get(v_b_2365_, 0);
                            leanh::lean_dec(v_unused_2395_);
                            v___x_2386_ = v_b_2365_;
                            v_isShared_2387_ = v_isSharedCheck_2394_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_2384_);
                            leanh::lean_dec(v_b_2365_);
                            v___x_2386_ = leanh::lean_box(0);
                            v_isShared_2387_ = v_isSharedCheck_2394_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_2365_;
                }
            }
            1 => {
                v___x_2368_ = 1usize;
                v___x_2369_ = lean_usize_add(v_i_2363_, v___x_2368_);
                v_i_2363_ = v___x_2369_;
                v_b_2365_ = v___y_2367_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2378_ = leanh::lean_box((v___x_2361_) as usize);
                if v_isShared_2377_ == 0 {
                    leanh::lean_ctor_set(v___x_2376_, 0, v___x_2378_);
                    v___x_2380_ = v___x_2376_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2381_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_snd_2374_);
                    v___x_2380_ = v_reuseFailAlloc_2381_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_2367_ = v___x_2380_;
                state = 1;
                continue;
            }
            4 => {
                v___x_2388_ = lean_array_uget_borrowed(v_as_2362_, v_i_2363_);
                leanh::lean_inc(v___x_2388_);
                v___x_2389_ = lean_array_push(v_snd_2384_, v___x_2388_);
                v___x_2390_ = leanh::lean_box((v___x_2371_) as usize);
                if v_isShared_2387_ == 0 {
                    leanh::lean_ctor_set(v___x_2386_, 1, v___x_2389_);
                    leanh::lean_ctor_set(v___x_2386_, 0, v___x_2390_);
                    v___x_2392_ = v___x_2386_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2393_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2393_, 1, v___x_2389_);
                    v___x_2392_ = v_reuseFailAlloc_2393_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2367_ = v___x_2392_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(
    mut v___x_2396_: *mut leanh::LeanObject,
    mut v_as_2397_: *mut leanh::LeanObject,
    mut v_i_2398_: *mut leanh::LeanObject,
    mut v_stop_2399_: *mut leanh::LeanObject,
    mut v_b_2400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4084__boxed_2401_: u8 = 0;
    let mut v_i_boxed_2402_: usize = 0;
    let mut v_stop_boxed_2403_: usize = 0;
    let mut v_res_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4084__boxed_2401_ = (leanh::lean_unbox(v___x_2396_) as u8);
    v_i_boxed_2402_ = leanh::lean_unbox_usize(v_i_2398_);
    leanh::lean_dec(v_i_2398_);
    v_stop_boxed_2403_ = leanh::lean_unbox_usize(v_stop_2399_);
    leanh::lean_dec(v_stop_2399_);
    v_res_2404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_4084__boxed_2401_, v_as_2397_, v_i_boxed_2402_, v_stop_boxed_2403_, v_b_2400_);
    leanh::lean_dec_ref(v_as_2397_);
    return v_res_2404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(
    mut v_sz_2412_: usize,
    mut v_i_2413_: usize,
    mut v_bs_2414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2415_: u8 = 0;
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: usize = 0;
    let mut v___x_2424_: usize = 0;
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2415_ = lean_usize_dec_lt(v_i_2413_, v_sz_2412_);
                if v___x_2415_ == 0 {
                    v___x_2416_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2416_, 0, v_bs_2414_);
                    return v___x_2416_;
                } else {
                    v_v_2417_ = lean_array_uget(v_bs_2414_, v_i_2413_);
                    v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3;
                    leanh::lean_inc(v_v_2417_);
                    v___x_2419_ = l_Lean_Syntax_isOfKind(v_v_2417_, v___x_2418_);
                    if v___x_2419_ == 0 {
                        leanh::lean_dec(v_v_2417_);
                        leanh::lean_dec_ref(v_bs_2414_);
                        v___x_2420_ = leanh::lean_box(0);
                        return v___x_2420_;
                    } else {
                        v___x_2421_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2422_ = lean_array_uset(v_bs_2414_, v_i_2413_, v___x_2421_);
                        v___x_2423_ = 1usize;
                        v___x_2424_ = lean_usize_add(v_i_2413_, v___x_2423_);
                        v___x_2425_ = lean_array_uset(v_bs_x27_2422_, v_i_2413_, v_v_2417_);
                        v_i_2413_ = v___x_2424_;
                        v_bs_2414_ = v___x_2425_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(
    mut v_sz_2427_: *mut leanh::LeanObject,
    mut v_i_2428_: *mut leanh::LeanObject,
    mut v_bs_2429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2430_: usize = 0;
    let mut v_i_boxed_2431_: usize = 0;
    let mut v_res_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2430_ = leanh::lean_unbox_usize(v_sz_2427_);
    leanh::lean_dec(v_sz_2427_);
    v_i_boxed_2431_ = leanh::lean_unbox_usize(v_i_2428_);
    leanh::lean_dec(v_i_2428_);
    v_res_2432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_2430_, v_i_boxed_2431_, v_bs_2429_);
    return v_res_2432_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2439_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2;
    v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
    return v___x_2440_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2447_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6;
    v___x_2448_ = l_Lean_stringToMessageData(v___x_2447_);
    return v___x_2448_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(
    mut v_kv_2451_: *mut leanh::LeanObject,
    mut v_a_2452_: *mut leanh::LeanObject,
    mut v_a_2453_: *mut leanh::LeanObject,
    mut v_a_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2470_: usize = 0;
    let mut v___x_2471_: usize = 0;
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tailKeyStx_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyTys_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currKey_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2502_: u8 = 0;
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2518_: u8 = 0;
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2542_: u8 = 0;
    let mut v_a_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2550_: u8 = 0;
    let mut v_isSharedCheck_2551_: u8 = 0;
    let mut v_unused_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2561_: u8 = 0;
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2565_: u8 = 0;
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut v_a_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2570_: u8 = 0;
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2574_: u8 = 0;
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: u8 = 0;
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: usize = 0;
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: usize = 0;
    let mut v___x_2588_: usize = 0;
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2456_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1;
                leanh::lean_inc(v_kv_2451_);
                v___x_2457_ = l_Lean_Syntax_isOfKind(v_kv_2451_, v___x_2456_);
                if v___x_2457_ == 0 {
                    v___x_2458_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
                    v___x_2459_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_2451_, v___x_2458_, v_a_2452_, v_a_2453_, v_a_2454_);
                    leanh::lean_dec_ref(v_a_2452_);
                    leanh::lean_dec(v_kv_2451_);
                    return v___x_2459_;
                } else {
                    v___x_2460_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2461_ = l_Lean_Syntax_getArg(v_kv_2451_, v___x_2460_);
                    v___x_2462_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5;
                    leanh::lean_inc(v___x_2461_);
                    v___x_2463_ = l_Lean_Syntax_isOfKind(v___x_2461_, v___x_2462_);
                    if v___x_2463_ == 0 {
                        leanh::lean_dec(v_kv_2451_);
                        v___x_2464_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                        v___x_2465_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2461_, v___x_2464_, v_a_2452_, v_a_2453_, v_a_2454_);
                        leanh::lean_dec_ref(v_a_2452_);
                        leanh::lean_dec(v___x_2461_);
                        return v___x_2465_;
                    } else {
                        v___x_2466_ = leanh::lean_unsigned_to_nat(2);
                        v_v_2467_ = l_Lean_Syntax_getArg(v_kv_2451_, v___x_2466_);
                        leanh::lean_dec(v_kv_2451_);
                        v___x_2575_ = l_Lean_Syntax_getArg(v___x_2461_, v___x_2460_);
                        v___x_2576_ = l_Lean_Syntax_getArgs(v___x_2575_);
                        leanh::lean_dec(v___x_2575_);
                        v___x_2577_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8;
                        v___x_2578_ = lean_array_get_size(v___x_2576_);
                        v___x_2579_ = lean_nat_dec_lt(v___x_2460_, v___x_2578_);
                        if v___x_2579_ == 0 {
                            leanh::lean_dec_ref(v___x_2576_);
                            v___y_2469_ = v___x_2577_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2580_ = leanh::lean_box((v___x_2463_) as usize);
                            v___x_2581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2581_, 0, v___x_2580_);
                            leanh::lean_ctor_set(v___x_2581_, 1, v___x_2577_);
                            v___x_2582_ = lean_nat_dec_le(v___x_2578_, v___x_2578_);
                            if v___x_2582_ == 0 {
                                if v___x_2579_ == 0 {
                                    leanh::lean_dec_ref_known(v___x_2581_, 2);
                                    leanh::lean_dec_ref(v___x_2576_);
                                    v___y_2469_ = v___x_2577_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2583_ = 0usize;
                                    v___x_2584_ = lean_usize_of_nat(v___x_2578_);
                                    v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2463_, v___x_2576_, v___x_2583_, v___x_2584_, v___x_2581_);
                                    leanh::lean_dec_ref(v___x_2576_);
                                    v_snd_2586_ = leanh::lean_ctor_get(v___x_2585_, 1);
                                    leanh::lean_inc(v_snd_2586_);
                                    leanh::lean_dec_ref(v___x_2585_);
                                    v___y_2469_ = v_snd_2586_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_2587_ = 0usize;
                                v___x_2588_ = lean_usize_of_nat(v___x_2578_);
                                v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2463_, v___x_2576_, v___x_2587_, v___x_2588_, v___x_2581_);
                                leanh::lean_dec_ref(v___x_2576_);
                                v_snd_2590_ = leanh::lean_ctor_get(v___x_2589_, 1);
                                leanh::lean_inc(v_snd_2590_);
                                leanh::lean_dec_ref(v___x_2589_);
                                v___y_2469_ = v_snd_2590_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_sz_2470_ = lean_array_size(v___y_2469_);
                v___x_2471_ = 0usize;
                v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_2470_, v___x_2471_, v___y_2469_);
                if leanh::lean_obj_tag(v___x_2472_) == 0 {
                    leanh::lean_dec(v_v_2467_);
                    v___x_2473_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                    v___x_2474_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2461_, v___x_2473_, v_a_2452_, v_a_2453_, v_a_2454_);
                    leanh::lean_dec_ref(v_a_2452_);
                    leanh::lean_dec(v___x_2461_);
                    return v___x_2474_;
                } else {
                    v_val_2475_ = leanh::lean_ctor_get(v___x_2472_, 0);
                    leanh::lean_inc(v_val_2475_);
                    leanh::lean_dec_ref_known(v___x_2472_, 1);
                    v___x_2476_ = leanh::lean_box(0);
                    v___x_2477_ = lean_array_get_size(v_val_2475_);
                    v___x_2478_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2479_ = lean_nat_sub(v___x_2477_, v___x_2478_);
                    v_tailKeyStx_2480_ = lean_array_get(v___x_2476_, v_val_2475_, v___x_2479_);
                    leanh::lean_dec(v___x_2479_);
                    v___x_2481_ = lean_array_pop(v_val_2475_);
                    v___x_2482_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(
                        v___x_2481_,
                        v_a_2452_,
                        v_a_2453_,
                        v_a_2454_,
                    );
                    leanh::lean_dec_ref(v___x_2481_);
                    if leanh::lean_obj_tag(v___x_2482_) == 0 {
                        v_a_2483_ = leanh::lean_ctor_get(v___x_2482_, 0);
                        leanh::lean_inc(v_a_2483_);
                        leanh::lean_dec_ref_known(v___x_2482_, 1);
                        v_fst_2484_ = leanh::lean_ctor_get(v_a_2483_, 0);
                        v_snd_2485_ = leanh::lean_ctor_get(v_a_2483_, 1);
                        v_isSharedCheck_2566_ = (!leanh::lean_is_exclusive(v_a_2483_)) as u8;
                        if v_isSharedCheck_2566_ == 0 {
                            v___x_2487_ = v_a_2483_;
                            v_isShared_2488_ = v_isSharedCheck_2566_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_2485_);
                            leanh::lean_inc(v_fst_2484_);
                            leanh::lean_dec(v_a_2483_);
                            v___x_2487_ = leanh::lean_box(0);
                            v_isShared_2488_ = v_isSharedCheck_2566_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_tailKeyStx_2480_);
                        leanh::lean_dec(v_v_2467_);
                        leanh::lean_dec(v___x_2461_);
                        v_a_2567_ = leanh::lean_ctor_get(v___x_2482_, 0);
                        v_isSharedCheck_2574_ =
                            (!leanh::lean_is_exclusive(v___x_2482_)) as u8;
                        if v_isSharedCheck_2574_ == 0 {
                            v___x_2569_ = v___x_2482_;
                            v_isShared_2570_ = v_isSharedCheck_2574_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2567_);
                            leanh::lean_dec(v___x_2482_);
                            v___x_2569_ = leanh::lean_box(0);
                            v_isShared_2570_ = v_isSharedCheck_2574_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_tailKeyStx_2480_);
                v___x_2489_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_2480_, v_a_2453_, v_a_2454_);
                if leanh::lean_obj_tag(v___x_2489_) == 0 {
                    v_a_2490_ = leanh::lean_ctor_get(v___x_2489_, 0);
                    leanh::lean_inc(v_a_2490_);
                    leanh::lean_dec_ref_known(v___x_2489_, 1);
                    v_keyTys_2491_ = leanh::lean_ctor_get(v_snd_2485_, 0);
                    v_arrKeyTys_2492_ = leanh::lean_ctor_get(v_snd_2485_, 1);
                    v_arrParents_2493_ = leanh::lean_ctor_get(v_snd_2485_, 2);
                    v_currArrKey_2494_ = leanh::lean_ctor_get(v_snd_2485_, 3);
                    v_currKey_2495_ = leanh::lean_ctor_get(v_snd_2485_, 4);
                    v_items_2496_ = leanh::lean_ctor_get(v_snd_2485_, 5);
                    v___x_2497_ = l_Lean_Name_str___override(v_fst_2484_, v_a_2490_);
                    v___x_2498_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_2491_, v___x_2497_);
                    if leanh::lean_obj_tag(v___x_2498_) == 1 {
                        leanh::lean_del_object(v___x_2487_);
                        leanh::lean_dec(v_v_2467_);
                        leanh::lean_dec(v___x_2461_);
                        v_val_2499_ = leanh::lean_ctor_get(v___x_2498_, 0);
                        v_isSharedCheck_2518_ =
                            (!leanh::lean_is_exclusive(v___x_2498_)) as u8;
                        if v_isSharedCheck_2518_ == 0 {
                            v___x_2501_ = v___x_2498_;
                            v_isShared_2502_ = v_isSharedCheck_2518_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2499_);
                            leanh::lean_dec(v___x_2498_);
                            v___x_2501_ = leanh::lean_box(0);
                            v_isShared_2502_ = v_isSharedCheck_2518_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_inc_ref(v_items_2496_);
                        leanh::lean_inc(v_currKey_2495_);
                        leanh::lean_inc(v_currArrKey_2494_);
                        leanh::lean_inc(v_arrParents_2493_);
                        leanh::lean_inc(v_arrKeyTys_2492_);
                        leanh::lean_inc(v_keyTys_2491_);
                        leanh::lean_dec(v___x_2498_);
                        leanh::lean_dec(v_tailKeyStx_2480_);
                        v_isSharedCheck_2551_ =
                            (!leanh::lean_is_exclusive(v_snd_2485_)) as u8;
                        if v_isSharedCheck_2551_ == 0 {
                            v_unused_2552_ = leanh::lean_ctor_get(v_snd_2485_, 5);
                            leanh::lean_dec(v_unused_2552_);
                            v_unused_2553_ = leanh::lean_ctor_get(v_snd_2485_, 4);
                            leanh::lean_dec(v_unused_2553_);
                            v_unused_2554_ = leanh::lean_ctor_get(v_snd_2485_, 3);
                            leanh::lean_dec(v_unused_2554_);
                            v_unused_2555_ = leanh::lean_ctor_get(v_snd_2485_, 2);
                            leanh::lean_dec(v_unused_2555_);
                            v_unused_2556_ = leanh::lean_ctor_get(v_snd_2485_, 1);
                            leanh::lean_dec(v_unused_2556_);
                            v_unused_2557_ = leanh::lean_ctor_get(v_snd_2485_, 0);
                            leanh::lean_dec(v_unused_2557_);
                            v___x_2520_ = v_snd_2485_;
                            v_isShared_2521_ = v_isSharedCheck_2551_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_snd_2485_);
                            v___x_2520_ = leanh::lean_box(0);
                            v_isShared_2521_ = v_isSharedCheck_2551_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2487_);
                    leanh::lean_dec(v_snd_2485_);
                    leanh::lean_dec(v_fst_2484_);
                    leanh::lean_dec(v_tailKeyStx_2480_);
                    leanh::lean_dec(v_v_2467_);
                    leanh::lean_dec(v___x_2461_);
                    v_a_2558_ = leanh::lean_ctor_get(v___x_2489_, 0);
                    v_isSharedCheck_2565_ = (!leanh::lean_is_exclusive(v___x_2489_)) as u8;
                    if v_isSharedCheck_2565_ == 0 {
                        v___x_2560_ = v___x_2489_;
                        v_isShared_2561_ = v_isSharedCheck_2565_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2558_);
                        leanh::lean_dec(v___x_2489_);
                        v___x_2560_ = leanh::lean_box(0);
                        v_isShared_2561_ = v_isSharedCheck_2565_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2503_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
                v___x_2504_ = (leanh::lean_unbox(v_val_2499_) as u8);
                leanh::lean_dec(v_val_2499_);
                v___x_2505_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_2504_);
                if v_isShared_2502_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2501_, 3);
                    leanh::lean_ctor_set(v___x_2501_, 0, v___x_2505_);
                    v___x_2507_ = v___x_2501_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2505_);
                    v___x_2507_ = v_reuseFailAlloc_2517_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2508_ = l_Lean_MessageData_ofFormat(v___x_2507_);
                v___x_2509_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2509_, 0, v___x_2503_);
                leanh::lean_ctor_set(v___x_2509_, 1, v___x_2508_);
                v___x_2510_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
                v___x_2511_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2511_, 0, v___x_2509_);
                leanh::lean_ctor_set(v___x_2511_, 1, v___x_2510_);
                v___x_2512_ = l_Lean_MessageData_ofName(v___x_2497_);
                v___x_2513_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2513_, 0, v___x_2511_);
                leanh::lean_ctor_set(v___x_2513_, 1, v___x_2512_);
                v___x_2514_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                v___x_2515_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2515_, 0, v___x_2513_);
                leanh::lean_ctor_set(v___x_2515_, 1, v___x_2514_);
                v___x_2516_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_2480_, v___x_2515_, v_snd_2485_, v_a_2453_, v_a_2454_);
                leanh::lean_dec(v_snd_2485_);
                leanh::lean_dec(v_tailKeyStx_2480_);
                return v___x_2516_;
            }
            5 => {
                v___x_2522_ = l_Lake_Toml_elabVal(v_v_2467_, v_a_2453_, v_a_2454_);
                if leanh::lean_obj_tag(v___x_2522_) == 0 {
                    v_a_2523_ = leanh::lean_ctor_get(v___x_2522_, 0);
                    v_isSharedCheck_2542_ = (!leanh::lean_is_exclusive(v___x_2522_)) as u8;
                    if v_isSharedCheck_2542_ == 0 {
                        v___x_2525_ = v___x_2522_;
                        v_isShared_2526_ = v_isSharedCheck_2542_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2523_);
                        leanh::lean_dec(v___x_2522_);
                        v___x_2525_ = leanh::lean_box(0);
                        v_isShared_2526_ = v_isSharedCheck_2542_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2520_);
                    leanh::lean_dec(v___x_2497_);
                    leanh::lean_dec_ref(v_items_2496_);
                    leanh::lean_dec(v_currKey_2495_);
                    leanh::lean_dec(v_currArrKey_2494_);
                    leanh::lean_dec(v_arrParents_2493_);
                    leanh::lean_dec(v_arrKeyTys_2492_);
                    leanh::lean_dec(v_keyTys_2491_);
                    leanh::lean_del_object(v___x_2487_);
                    leanh::lean_dec(v___x_2461_);
                    v_a_2543_ = leanh::lean_ctor_get(v___x_2522_, 0);
                    v_isSharedCheck_2550_ = (!leanh::lean_is_exclusive(v___x_2522_)) as u8;
                    if v_isSharedCheck_2550_ == 0 {
                        v___x_2545_ = v___x_2522_;
                        v_isShared_2546_ = v_isSharedCheck_2550_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2543_);
                        leanh::lean_dec(v___x_2522_);
                        v___x_2545_ = leanh::lean_box(0);
                        v_isShared_2546_ = v_isSharedCheck_2550_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2527_ = leanh::lean_box(0);
                v___x_2528_ = 0;
                v___x_2529_ = leanh::lean_box((v___x_2528_) as usize);
                leanh::lean_inc(v___x_2497_);
                v___x_2530_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2497_, v___x_2529_, v_keyTys_2491_);
                v___x_2531_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2531_, 0, v___x_2461_);
                leanh::lean_ctor_set(v___x_2531_, 1, v___x_2497_);
                leanh::lean_ctor_set(v___x_2531_, 2, v_a_2523_);
                v___x_2532_ = lean_array_push(v_items_2496_, v___x_2531_);
                if v_isShared_2521_ == 0 {
                    leanh::lean_ctor_set(v___x_2520_, 5, v___x_2532_);
                    leanh::lean_ctor_set(v___x_2520_, 0, v___x_2530_);
                    v___x_2534_ = v___x_2520_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2541_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_arrKeyTys_2492_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_arrParents_2493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 3, v_currArrKey_2494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 4, v_currKey_2495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 5, v___x_2532_);
                    v___x_2534_ = v_reuseFailAlloc_2541_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2488_ == 0 {
                    leanh::lean_ctor_set(v___x_2487_, 1, v___x_2534_);
                    leanh::lean_ctor_set(v___x_2487_, 0, v___x_2527_);
                    v___x_2536_ = v___x_2487_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___x_2534_);
                    v___x_2536_ = v_reuseFailAlloc_2540_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2526_ == 0 {
                    leanh::lean_ctor_set(v___x_2525_, 0, v___x_2536_);
                    v___x_2538_ = v___x_2525_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2539_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
                    v___x_2538_ = v_reuseFailAlloc_2539_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2538_;
            }
            10 => {
                if v_isShared_2546_ == 0 {
                    v___x_2548_ = v___x_2545_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2549_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
                    v___x_2548_ = v_reuseFailAlloc_2549_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2548_;
            }
            12 => {
                if v_isShared_2561_ == 0 {
                    v___x_2563_ = v___x_2560_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2564_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
                    v___x_2563_ = v_reuseFailAlloc_2564_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2563_;
            }
            14 => {
                if v_isShared_2570_ == 0 {
                    v___x_2572_ = v___x_2569_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2573_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
                    v___x_2572_ = v_reuseFailAlloc_2573_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(
    mut v_kv_2591_: *mut leanh::LeanObject,
    mut v_a_2592_: *mut leanh::LeanObject,
    mut v_a_2593_: *mut leanh::LeanObject,
    mut v_a_2594_: *mut leanh::LeanObject,
    mut v_a_2595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2596_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(
        v_kv_2591_, v_a_2592_, v_a_2593_, v_a_2594_,
    );
    leanh::lean_dec(v_a_2594_);
    leanh::lean_dec_ref(v_a_2593_);
    return v_res_2596_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0;
    v___x_2599_ = l_Lean_stringToMessageData(v___x_2598_);
    return v___x_2599_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(
    mut v_as_2600_: *mut leanh::LeanObject,
    mut v_i_2601_: usize,
    mut v_stop_2602_: usize,
    mut v_b_2603_: *mut leanh::LeanObject,
    mut v___y_2604_: *mut leanh::LeanObject,
    mut v___y_2605_: *mut leanh::LeanObject,
    mut v___y_2606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: usize = 0;
    let mut v___x_2612_: usize = 0;
    let mut v___x_2614_: u8 = 0;
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyTys_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currKey_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2630_: u8 = 0;
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2633_: u8 = 0;
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2650_: u8 = 0;
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2654_: u8 = 0;
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_unused_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: u8 = 0;
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2685_: u8 = 0;
    let mut v_reuseFailAlloc_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2687_: u8 = 0;
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2690_: u8 = 0;
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_unused_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2707_: u8 = 0;
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2711_: u8 = 0;
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2614_ = lean_usize_dec_eq(v_i_2601_, v_stop_2602_);
                if v___x_2614_ == 0 {
                    v___x_2615_ = lean_array_uget_borrowed(v_as_2600_, v_i_2601_);
                    leanh::lean_inc(v___x_2615_);
                    v___x_2616_ = l_Lake_Toml_elabSimpleKey(v___x_2615_, v___y_2605_, v___y_2606_);
                    if leanh::lean_obj_tag(v___x_2616_) == 0 {
                        v_a_2617_ = leanh::lean_ctor_get(v___x_2616_, 0);
                        leanh::lean_inc(v_a_2617_);
                        leanh::lean_dec_ref_known(v___x_2616_, 1);
                        v_keyTys_2618_ = leanh::lean_ctor_get(v___y_2604_, 0);
                        v_arrKeyTys_2619_ = leanh::lean_ctor_get(v___y_2604_, 1);
                        v_arrParents_2620_ = leanh::lean_ctor_get(v___y_2604_, 2);
                        v_currArrKey_2621_ = leanh::lean_ctor_get(v___y_2604_, 3);
                        v_currKey_2622_ = leanh::lean_ctor_get(v___y_2604_, 4);
                        v_items_2623_ = leanh::lean_ctor_get(v___y_2604_, 5);
                        v___x_2624_ = l_Lean_Name_str___override(v_b_2603_, v_a_2617_);
                        v___x_2625_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_2618_, v___x_2624_);
                        if leanh::lean_obj_tag(v___x_2625_) == 1 {
                            v_val_2626_ = leanh::lean_ctor_get(v___x_2625_, 0);
                            v_isSharedCheck_2687_ =
                                (!leanh::lean_is_exclusive(v___x_2625_)) as u8;
                            if v_isSharedCheck_2687_ == 0 {
                                v___x_2628_ = v___x_2625_;
                                v_isShared_2629_ = v_isSharedCheck_2687_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_2626_);
                                leanh::lean_dec(v___x_2625_);
                                v___x_2628_ = leanh::lean_box(0);
                                v_isShared_2629_ = v_isSharedCheck_2687_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_inc_ref(v_items_2623_);
                            leanh::lean_inc(v_currKey_2622_);
                            leanh::lean_inc(v_currArrKey_2621_);
                            leanh::lean_inc(v_arrParents_2620_);
                            leanh::lean_inc(v_arrKeyTys_2619_);
                            leanh::lean_inc(v_keyTys_2618_);
                            leanh::lean_dec(v___x_2625_);
                            v_isSharedCheck_2697_ =
                                (!leanh::lean_is_exclusive(v___y_2604_)) as u8;
                            if v_isSharedCheck_2697_ == 0 {
                                v_unused_2698_ = leanh::lean_ctor_get(v___y_2604_, 5);
                                leanh::lean_dec(v_unused_2698_);
                                v_unused_2699_ = leanh::lean_ctor_get(v___y_2604_, 4);
                                leanh::lean_dec(v_unused_2699_);
                                v_unused_2700_ = leanh::lean_ctor_get(v___y_2604_, 3);
                                leanh::lean_dec(v_unused_2700_);
                                v_unused_2701_ = leanh::lean_ctor_get(v___y_2604_, 2);
                                leanh::lean_dec(v_unused_2701_);
                                v_unused_2702_ = leanh::lean_ctor_get(v___y_2604_, 1);
                                leanh::lean_dec(v_unused_2702_);
                                v_unused_2703_ = leanh::lean_ctor_get(v___y_2604_, 0);
                                leanh::lean_dec(v_unused_2703_);
                                v___x_2689_ = v___y_2604_;
                                v_isShared_2690_ = v_isSharedCheck_2697_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_dec(v___y_2604_);
                                v___x_2689_ = leanh::lean_box(0);
                                v_isShared_2690_ = v_isSharedCheck_2697_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_2604_);
                        leanh::lean_dec(v_b_2603_);
                        v_a_2704_ = leanh::lean_ctor_get(v___x_2616_, 0);
                        v_isSharedCheck_2711_ =
                            (!leanh::lean_is_exclusive(v___x_2616_)) as u8;
                        if v_isSharedCheck_2711_ == 0 {
                            v___x_2706_ = v___x_2616_;
                            v_isShared_2707_ = v_isSharedCheck_2711_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2704_);
                            leanh::lean_dec(v___x_2616_);
                            v___x_2706_ = leanh::lean_box(0);
                            v_isShared_2707_ = v_isSharedCheck_2711_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    v___x_2712_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2712_, 0, v_b_2603_);
                    leanh::lean_ctor_set(v___x_2712_, 1, v___y_2604_);
                    v___x_2713_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2713_, 0, v___x_2712_);
                    return v___x_2713_;
                }
            }
            1 => {
                v___x_2611_ = 1usize;
                v___x_2612_ = lean_usize_add(v_i_2601_, v___x_2611_);
                v_i_2601_ = v___x_2612_;
                v_b_2603_ = v_fst_2609_;
                v___y_2604_ = v_snd_2610_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2630_ = (leanh::lean_unbox(v_val_2626_) as u8);
                match v___x_2630_ {
                    2 => {
                        leanh::lean_inc_ref(v_items_2623_);
                        leanh::lean_inc(v_currKey_2622_);
                        leanh::lean_inc(v_arrParents_2620_);
                        leanh::lean_inc(v_arrKeyTys_2619_);
                        leanh::lean_del_object(v___x_2628_);
                        leanh::lean_dec(v_val_2626_);
                        v_isSharedCheck_2655_ =
                            (!leanh::lean_is_exclusive(v___y_2604_)) as u8;
                        if v_isSharedCheck_2655_ == 0 {
                            v_unused_2656_ = leanh::lean_ctor_get(v___y_2604_, 5);
                            leanh::lean_dec(v_unused_2656_);
                            v_unused_2657_ = leanh::lean_ctor_get(v___y_2604_, 4);
                            leanh::lean_dec(v_unused_2657_);
                            v_unused_2658_ = leanh::lean_ctor_get(v___y_2604_, 3);
                            leanh::lean_dec(v_unused_2658_);
                            v_unused_2659_ = leanh::lean_ctor_get(v___y_2604_, 2);
                            leanh::lean_dec(v_unused_2659_);
                            v_unused_2660_ = leanh::lean_ctor_get(v___y_2604_, 1);
                            leanh::lean_dec(v_unused_2660_);
                            v_unused_2661_ = leanh::lean_ctor_get(v___y_2604_, 0);
                            leanh::lean_dec(v_unused_2661_);
                            v___x_2632_ = v___y_2604_;
                            v_isShared_2633_ = v_isSharedCheck_2655_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___y_2604_);
                            v___x_2632_ = leanh::lean_box(0);
                            v_isShared_2633_ = v_isSharedCheck_2655_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        leanh::lean_del_object(v___x_2628_);
                        leanh::lean_dec(v_val_2626_);
                        v_fst_2609_ = v___x_2624_;
                        v_snd_2610_ = v___y_2604_;
                        state = 1;
                        continue;
                    }
                    4 => {
                        leanh::lean_del_object(v___x_2628_);
                        leanh::lean_dec(v_val_2626_);
                        v_fst_2609_ = v___x_2624_;
                        v_snd_2610_ = v___y_2604_;
                        state = 1;
                        continue;
                    }
                    3 => {
                        leanh::lean_del_object(v___x_2628_);
                        leanh::lean_dec(v_val_2626_);
                        v_fst_2609_ = v___x_2624_;
                        v_snd_2610_ = v___y_2604_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2662_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
                        v___x_2663_ = (leanh::lean_unbox(v_val_2626_) as u8);
                        leanh::lean_dec(v_val_2626_);
                        v___x_2664_ =
                            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(
                                v___x_2663_,
                            );
                        if v_isShared_2629_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_2628_, 3);
                            leanh::lean_ctor_set(v___x_2628_, 0, v___x_2664_);
                            v___x_2666_ = v___x_2628_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_2686_ =
                                leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2664_);
                            v___x_2666_ = v_reuseFailAlloc_2686_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2634_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_2619_, v___x_2624_);
                if leanh::lean_obj_tag(v___x_2634_) == 1 {
                    v_val_2635_ = leanh::lean_ctor_get(v___x_2634_, 0);
                    leanh::lean_inc(v_val_2635_);
                    leanh::lean_dec_ref_known(v___x_2634_, 1);
                    leanh::lean_inc(v___x_2624_);
                    if v_isShared_2633_ == 0 {
                        leanh::lean_ctor_set(v___x_2632_, 3, v___x_2624_);
                        leanh::lean_ctor_set(v___x_2632_, 0, v_val_2635_);
                        v___x_2637_ = v___x_2632_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2638_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_val_2635_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_arrKeyTys_2619_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2638_, 2, v_arrParents_2620_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2638_, 3, v___x_2624_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2638_, 4, v_currKey_2622_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2638_, 5, v_items_2623_);
                        v___x_2637_ = v_reuseFailAlloc_2638_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2634_);
                    leanh::lean_del_object(v___x_2632_);
                    leanh::lean_dec_ref(v_items_2623_);
                    leanh::lean_dec(v_currKey_2622_);
                    leanh::lean_dec(v_arrParents_2620_);
                    leanh::lean_dec(v_arrKeyTys_2619_);
                    v___x_2639_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
                    leanh::lean_inc(v___x_2624_);
                    v___x_2640_ = l_Lean_MessageData_ofName(v___x_2624_);
                    v___x_2641_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2641_, 0, v___x_2639_);
                    leanh::lean_ctor_set(v___x_2641_, 1, v___x_2640_);
                    v___x_2642_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                    v___x_2643_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2643_, 0, v___x_2641_);
                    leanh::lean_ctor_set(v___x_2643_, 1, v___x_2642_);
                    v___x_2644_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_2643_, v___y_2605_, v___y_2606_);
                    if leanh::lean_obj_tag(v___x_2644_) == 0 {
                        v_a_2645_ = leanh::lean_ctor_get(v___x_2644_, 0);
                        leanh::lean_inc(v_a_2645_);
                        leanh::lean_dec_ref_known(v___x_2644_, 1);
                        v_snd_2646_ = leanh::lean_ctor_get(v_a_2645_, 1);
                        leanh::lean_inc(v_snd_2646_);
                        leanh::lean_dec(v_a_2645_);
                        v_fst_2609_ = v___x_2624_;
                        v_snd_2610_ = v_snd_2646_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2624_);
                        v_a_2647_ = leanh::lean_ctor_get(v___x_2644_, 0);
                        v_isSharedCheck_2654_ =
                            (!leanh::lean_is_exclusive(v___x_2644_)) as u8;
                        if v_isSharedCheck_2654_ == 0 {
                            v___x_2649_ = v___x_2644_;
                            v_isShared_2650_ = v_isSharedCheck_2654_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2647_);
                            leanh::lean_dec(v___x_2644_);
                            v___x_2649_ = leanh::lean_box(0);
                            v_isShared_2650_ = v_isSharedCheck_2654_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v_fst_2609_ = v___x_2624_;
                v_snd_2610_ = v___x_2637_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_2650_ == 0 {
                    v___x_2652_ = v___x_2649_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2653_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
                    v___x_2652_ = v_reuseFailAlloc_2653_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2652_;
            }
            7 => {
                v___x_2667_ = l_Lean_MessageData_ofFormat(v___x_2666_);
                v___x_2668_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2668_, 0, v___x_2662_);
                leanh::lean_ctor_set(v___x_2668_, 1, v___x_2667_);
                v___x_2669_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
                v___x_2670_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2670_, 0, v___x_2668_);
                leanh::lean_ctor_set(v___x_2670_, 1, v___x_2669_);
                leanh::lean_inc(v___x_2624_);
                v___x_2671_ = l_Lean_MessageData_ofName(v___x_2624_);
                v___x_2672_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2672_, 0, v___x_2670_);
                leanh::lean_ctor_set(v___x_2672_, 1, v___x_2671_);
                v___x_2673_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                v___x_2674_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2674_, 0, v___x_2672_);
                leanh::lean_ctor_set(v___x_2674_, 1, v___x_2673_);
                v___x_2675_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2615_, v___x_2674_, v___y_2604_, v___y_2605_, v___y_2606_);
                leanh::lean_dec_ref(v___y_2604_);
                if leanh::lean_obj_tag(v___x_2675_) == 0 {
                    v_a_2676_ = leanh::lean_ctor_get(v___x_2675_, 0);
                    leanh::lean_inc(v_a_2676_);
                    leanh::lean_dec_ref_known(v___x_2675_, 1);
                    v_snd_2677_ = leanh::lean_ctor_get(v_a_2676_, 1);
                    leanh::lean_inc(v_snd_2677_);
                    leanh::lean_dec(v_a_2676_);
                    v_fst_2609_ = v___x_2624_;
                    v_snd_2610_ = v_snd_2677_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2624_);
                    v_a_2678_ = leanh::lean_ctor_get(v___x_2675_, 0);
                    v_isSharedCheck_2685_ = (!leanh::lean_is_exclusive(v___x_2675_)) as u8;
                    if v_isSharedCheck_2685_ == 0 {
                        v___x_2680_ = v___x_2675_;
                        v_isShared_2681_ = v_isSharedCheck_2685_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2678_);
                        leanh::lean_dec(v___x_2675_);
                        v___x_2680_ = leanh::lean_box(0);
                        v_isShared_2681_ = v_isSharedCheck_2685_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2681_ == 0 {
                    v___x_2683_ = v___x_2680_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2684_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
                    v___x_2683_ = v_reuseFailAlloc_2684_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2683_;
            }
            10 => {
                v___x_2691_ = 4;
                v___x_2692_ = leanh::lean_box((v___x_2691_) as usize);
                leanh::lean_inc(v___x_2624_);
                v___x_2693_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2624_, v___x_2692_, v_keyTys_2618_);
                if v_isShared_2690_ == 0 {
                    leanh::lean_ctor_set(v___x_2689_, 0, v___x_2693_);
                    v___x_2695_ = v___x_2689_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2696_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_arrKeyTys_2619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_arrParents_2620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_currArrKey_2621_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 4, v_currKey_2622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 5, v_items_2623_);
                    v___x_2695_ = v_reuseFailAlloc_2696_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_fst_2609_ = v___x_2624_;
                v_snd_2610_ = v___x_2695_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_2707_ == 0 {
                    v___x_2709_ = v___x_2706_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
                    v___x_2709_ = v_reuseFailAlloc_2710_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(
    mut v_as_2714_: *mut leanh::LeanObject,
    mut v_i_2715_: *mut leanh::LeanObject,
    mut v_stop_2716_: *mut leanh::LeanObject,
    mut v_b_2717_: *mut leanh::LeanObject,
    mut v___y_2718_: *mut leanh::LeanObject,
    mut v___y_2719_: *mut leanh::LeanObject,
    mut v___y_2720_: *mut leanh::LeanObject,
    mut v___y_2721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2722_: usize = 0;
    let mut v_stop_boxed_2723_: usize = 0;
    let mut v_res_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2722_ = leanh::lean_unbox_usize(v_i_2715_);
    leanh::lean_dec(v_i_2715_);
    v_stop_boxed_2723_ = leanh::lean_unbox_usize(v_stop_2716_);
    leanh::lean_dec(v_stop_2716_);
    v_res_2724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_2714_, v_i_boxed_2722_, v_stop_boxed_2723_, v_b_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
    leanh::lean_dec(v___y_2720_);
    leanh::lean_dec_ref(v___y_2719_);
    leanh::lean_dec_ref(v_as_2714_);
    return v_res_2724_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(
    mut v_t_2725_: *mut leanh::LeanObject,
    mut v_k_2726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: u8 = 0;
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2725_) == 0 {
                    v_k_2727_ = leanh::lean_ctor_get(v_t_2725_, 1);
                    v_v_2728_ = leanh::lean_ctor_get(v_t_2725_, 2);
                    v_l_2729_ = leanh::lean_ctor_get(v_t_2725_, 3);
                    v_r_2730_ = leanh::lean_ctor_get(v_t_2725_, 4);
                    v___x_2731_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2726_, v_k_2727_);
                    match v___x_2731_ {
                        0 => {
                            v_t_2725_ = v_l_2729_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_2728_);
                            v___x_2733_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2733_, 0, v_v_2728_);
                            return v___x_2733_;
                        }
                        _ => {
                            v_t_2725_ = v_r_2730_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2735_ = leanh::lean_box(0);
                    return v___x_2735_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(
    mut v_t_2736_: *mut leanh::LeanObject,
    mut v_k_2737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2738_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_2736_, v_k_2737_);
    leanh::lean_dec(v_k_2737_);
    leanh::lean_dec(v_t_2736_);
    return v_res_2738_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(
    mut v_ks_2739_: *mut leanh::LeanObject,
    mut v_a_2740_: *mut leanh::LeanObject,
    mut v_a_2741_: *mut leanh::LeanObject,
    mut v_a_2742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyTys_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currKey_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v_arrKeyTys_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: u8 = 0;
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: usize = 0;
    let mut v___x_2768_: usize = 0;
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: usize = 0;
    let mut v___x_2771_: usize = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_keyTys_2744_ = leanh::lean_ctor_get(v_a_2740_, 0);
                v_arrKeyTys_2745_ = leanh::lean_ctor_get(v_a_2740_, 1);
                v_arrParents_2746_ = leanh::lean_ctor_get(v_a_2740_, 2);
                v_currArrKey_2747_ = leanh::lean_ctor_get(v_a_2740_, 3);
                v_currKey_2748_ = leanh::lean_ctor_get(v_a_2740_, 4);
                v_items_2749_ = leanh::lean_ctor_get(v_a_2740_, 5);
                v_isSharedCheck_2777_ = (!leanh::lean_is_exclusive(v_a_2740_)) as u8;
                if v_isSharedCheck_2777_ == 0 {
                    v___x_2751_ = v_a_2740_;
                    v_isShared_2752_ = v_isSharedCheck_2777_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_items_2749_);
                    leanh::lean_inc(v_currKey_2748_);
                    leanh::lean_inc(v_currArrKey_2747_);
                    leanh::lean_inc(v_arrParents_2746_);
                    leanh::lean_inc(v_arrKeyTys_2745_);
                    leanh::lean_inc(v_keyTys_2744_);
                    leanh::lean_dec(v_a_2740_);
                    v___x_2751_ = leanh::lean_box(0);
                    v_isShared_2752_ = v_isSharedCheck_2777_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_arrKeyTys_2753_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_2747_, v_keyTys_2744_, v_arrKeyTys_2745_);
                v___x_2754_ = leanh::lean_box(0);
                v___x_2774_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_2753_, v___x_2754_);
                if leanh::lean_obj_tag(v___x_2774_) == 0 {
                    v___x_2775_ = leanh::lean_box(1);
                    v___y_2756_ = v___x_2775_;
                    state = 2;
                    continue;
                } else {
                    v_val_2776_ = leanh::lean_ctor_get(v___x_2774_, 0);
                    leanh::lean_inc(v_val_2776_);
                    leanh::lean_dec_ref_known(v___x_2774_, 1);
                    v___y_2756_ = v_val_2776_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2752_ == 0 {
                    leanh::lean_ctor_set(v___x_2751_, 3, v___x_2754_);
                    leanh::lean_ctor_set(v___x_2751_, 1, v_arrKeyTys_2753_);
                    leanh::lean_ctor_set(v___x_2751_, 0, v___y_2756_);
                    v___x_2758_ = v___x_2751_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2773_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___y_2756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_arrKeyTys_2753_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_arrParents_2746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 3, v___x_2754_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 4, v_currKey_2748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 5, v_items_2749_);
                    v___x_2758_ = v_reuseFailAlloc_2773_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2759_ = leanh::lean_unsigned_to_nat(0);
                v___x_2760_ = lean_array_get_size(v_ks_2739_);
                v___x_2761_ = lean_nat_dec_lt(v___x_2759_, v___x_2760_);
                if v___x_2761_ == 0 {
                    v___x_2762_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2762_, 0, v___x_2754_);
                    leanh::lean_ctor_set(v___x_2762_, 1, v___x_2758_);
                    v___x_2763_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2763_, 0, v___x_2762_);
                    return v___x_2763_;
                } else {
                    v___x_2764_ = lean_nat_dec_le(v___x_2760_, v___x_2760_);
                    if v___x_2764_ == 0 {
                        if v___x_2761_ == 0 {
                            v___x_2765_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2765_, 0, v___x_2754_);
                            leanh::lean_ctor_set(v___x_2765_, 1, v___x_2758_);
                            v___x_2766_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2766_, 0, v___x_2765_);
                            return v___x_2766_;
                        } else {
                            v___x_2767_ = 0usize;
                            v___x_2768_ = lean_usize_of_nat(v___x_2760_);
                            v___x_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_2739_, v___x_2767_, v___x_2768_, v___x_2754_, v___x_2758_, v_a_2741_, v_a_2742_);
                            return v___x_2769_;
                        }
                    } else {
                        v___x_2770_ = 0usize;
                        v___x_2771_ = lean_usize_of_nat(v___x_2760_);
                        v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_2739_, v___x_2770_, v___x_2771_, v___x_2754_, v___x_2758_, v_a_2741_, v_a_2742_);
                        return v___x_2772_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(
    mut v_ks_2778_: *mut leanh::LeanObject,
    mut v_a_2779_: *mut leanh::LeanObject,
    mut v_a_2780_: *mut leanh::LeanObject,
    mut v_a_2781_: *mut leanh::LeanObject,
    mut v_a_2782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2783_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(
        v_ks_2778_, v_a_2779_, v_a_2780_, v_a_2781_,
    );
    leanh::lean_dec(v_a_2781_);
    leanh::lean_dec_ref(v_a_2780_);
    leanh::lean_dec_ref(v_ks_2778_);
    return v_res_2783_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(
    mut v_00_u03b4_2784_: *mut leanh::LeanObject,
    mut v_t_2785_: *mut leanh::LeanObject,
    mut v_k_2786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2787_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_2785_, v_k_2786_);
    return v___x_2787_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(
    mut v_00_u03b4_2788_: *mut leanh::LeanObject,
    mut v_t_2789_: *mut leanh::LeanObject,
    mut v_k_2790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2791_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_2788_, v_t_2789_, v_k_2790_);
    leanh::lean_dec(v_k_2790_);
    leanh::lean_dec(v_t_2789_);
    return v_res_2791_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2793_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0;
    v___x_2794_ = l_Lake_Toml_RBDict_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2793_,
    );
    return v___x_2794_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2801_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4;
    v___x_2802_ = l_Lean_stringToMessageData(v___x_2801_);
    return v___x_2802_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(
    mut v_x_2803_: *mut leanh::LeanObject,
    mut v_a_2804_: *mut leanh::LeanObject,
    mut v_a_2805_: *mut leanh::LeanObject,
    mut v_a_2806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyTys_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: u8 = 0;
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2838_: u8 = 0;
    let mut v_cancelTk_x3f_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2840_: u8 = 0;
    let mut v_inheritedTraceOptions_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: u8 = 0;
    let mut v_ref_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2852_: usize = 0;
    let mut v___x_2853_: usize = 0;
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tailKey_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyTys_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2882_: u8 = 0;
    let mut v___x_2883_: u8 = 0;
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: u8 = 0;
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v_a_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2909_: u8 = 0;
    let mut v_isSharedCheck_2910_: u8 = 0;
    let mut v_a_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2914_: u8 = 0;
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2918_: u8 = 0;
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: u8 = 0;
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: u8 = 0;
    let mut v___x_2932_: usize = 0;
    let mut v___x_2933_: usize = 0;
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: usize = 0;
    let mut v___x_2937_: usize = 0;
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2826_ = leanh::lean_ctor_get(v_a_2805_, 0);
                v_fileMap_2827_ = leanh::lean_ctor_get(v_a_2805_, 1);
                v_options_2828_ = leanh::lean_ctor_get(v_a_2805_, 2);
                v_currRecDepth_2829_ = leanh::lean_ctor_get(v_a_2805_, 3);
                v_maxRecDepth_2830_ = leanh::lean_ctor_get(v_a_2805_, 4);
                v_ref_2831_ = leanh::lean_ctor_get(v_a_2805_, 5);
                v_currNamespace_2832_ = leanh::lean_ctor_get(v_a_2805_, 6);
                v_openDecls_2833_ = leanh::lean_ctor_get(v_a_2805_, 7);
                v_initHeartbeats_2834_ = leanh::lean_ctor_get(v_a_2805_, 8);
                v_maxHeartbeats_2835_ = leanh::lean_ctor_get(v_a_2805_, 9);
                v_quotContext_2836_ = leanh::lean_ctor_get(v_a_2805_, 10);
                v_currMacroScope_2837_ = leanh::lean_ctor_get(v_a_2805_, 11);
                v_diag_2838_ = leanh::lean_ctor_get_uint8(
                    v_a_2805_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2839_ = leanh::lean_ctor_get(v_a_2805_, 12);
                v_suppressElabErrors_2840_ = leanh::lean_ctor_get_uint8(
                    v_a_2805_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2841_ = leanh::lean_ctor_get(v_a_2805_, 13);
                v___x_2842_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3;
                leanh::lean_inc(v_x_2803_);
                v___x_2843_ = l_Lean_Syntax_isOfKind(v_x_2803_, v___x_2842_);
                v_ref_2844_ = l_Lean_replaceRef(v_x_2803_, v_ref_2831_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_2841_);
                leanh::lean_inc(v_cancelTk_x3f_2839_);
                leanh::lean_inc(v_currMacroScope_2837_);
                leanh::lean_inc(v_quotContext_2836_);
                leanh::lean_inc(v_maxHeartbeats_2835_);
                leanh::lean_inc(v_initHeartbeats_2834_);
                leanh::lean_inc(v_openDecls_2833_);
                leanh::lean_inc(v_currNamespace_2832_);
                leanh::lean_inc(v_maxRecDepth_2830_);
                leanh::lean_inc(v_currRecDepth_2829_);
                leanh::lean_inc_ref(v_options_2828_);
                leanh::lean_inc_ref(v_fileMap_2827_);
                leanh::lean_inc_ref(v_fileName_2826_);
                v___x_2845_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2845_, 0, v_fileName_2826_);
                leanh::lean_ctor_set(v___x_2845_, 1, v_fileMap_2827_);
                leanh::lean_ctor_set(v___x_2845_, 2, v_options_2828_);
                leanh::lean_ctor_set(v___x_2845_, 3, v_currRecDepth_2829_);
                leanh::lean_ctor_set(v___x_2845_, 4, v_maxRecDepth_2830_);
                leanh::lean_ctor_set(v___x_2845_, 5, v_ref_2844_);
                leanh::lean_ctor_set(v___x_2845_, 6, v_currNamespace_2832_);
                leanh::lean_ctor_set(v___x_2845_, 7, v_openDecls_2833_);
                leanh::lean_ctor_set(v___x_2845_, 8, v_initHeartbeats_2834_);
                leanh::lean_ctor_set(v___x_2845_, 9, v_maxHeartbeats_2835_);
                leanh::lean_ctor_set(v___x_2845_, 10, v_quotContext_2836_);
                leanh::lean_ctor_set(v___x_2845_, 11, v_currMacroScope_2837_);
                leanh::lean_ctor_set(v___x_2845_, 12, v_cancelTk_x3f_2839_);
                leanh::lean_ctor_set(v___x_2845_, 13, v_inheritedTraceOptions_2841_);
                leanh::lean_ctor_set_uint8(
                    v___x_2845_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_2838_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2845_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2840_,
                );
                if v___x_2843_ == 0 {
                    v___x_2846_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5);
                    v___x_2847_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_2803_, v___x_2846_, v_a_2804_, v___x_2845_, v_a_2806_);
                    leanh::lean_dec_ref_known(v___x_2845_, 14);
                    leanh::lean_dec_ref(v_a_2804_);
                    leanh::lean_dec(v_x_2803_);
                    return v___x_2847_;
                } else {
                    v___x_2848_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2849_ = l_Lean_Syntax_getArg(v_x_2803_, v___x_2848_);
                    v___x_2919_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5;
                    leanh::lean_inc(v___x_2849_);
                    v___x_2920_ = l_Lean_Syntax_isOfKind(v___x_2849_, v___x_2919_);
                    if v___x_2920_ == 0 {
                        leanh::lean_dec(v_x_2803_);
                        v___x_2921_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                        v___x_2922_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2849_, v___x_2921_, v_a_2804_, v___x_2845_, v_a_2806_);
                        leanh::lean_dec_ref_known(v___x_2845_, 14);
                        leanh::lean_dec_ref(v_a_2804_);
                        leanh::lean_dec(v___x_2849_);
                        return v___x_2922_;
                    } else {
                        v___x_2923_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2924_ = l_Lean_Syntax_getArg(v___x_2849_, v___x_2923_);
                        v___x_2925_ = l_Lean_Syntax_getArgs(v___x_2924_);
                        leanh::lean_dec(v___x_2924_);
                        v___x_2926_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8;
                        v___x_2927_ = lean_array_get_size(v___x_2925_);
                        v___x_2928_ = lean_nat_dec_lt(v___x_2923_, v___x_2927_);
                        if v___x_2928_ == 0 {
                            leanh::lean_dec_ref(v___x_2925_);
                            v___y_2851_ = v___x_2926_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2929_ = leanh::lean_box((v___x_2920_) as usize);
                            v___x_2930_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2930_, 0, v___x_2929_);
                            leanh::lean_ctor_set(v___x_2930_, 1, v___x_2926_);
                            v___x_2931_ = lean_nat_dec_le(v___x_2927_, v___x_2927_);
                            if v___x_2931_ == 0 {
                                if v___x_2928_ == 0 {
                                    leanh::lean_dec_ref_known(v___x_2930_, 2);
                                    leanh::lean_dec_ref(v___x_2925_);
                                    v___y_2851_ = v___x_2926_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2932_ = 0usize;
                                    v___x_2933_ = lean_usize_of_nat(v___x_2927_);
                                    v___x_2934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2920_, v___x_2925_, v___x_2932_, v___x_2933_, v___x_2930_);
                                    leanh::lean_dec_ref(v___x_2925_);
                                    v_snd_2935_ = leanh::lean_ctor_get(v___x_2934_, 1);
                                    leanh::lean_inc(v_snd_2935_);
                                    leanh::lean_dec_ref(v___x_2934_);
                                    v___y_2851_ = v_snd_2935_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_2936_ = 0usize;
                                v___x_2937_ = lean_usize_of_nat(v___x_2927_);
                                v___x_2938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2920_, v___x_2925_, v___x_2936_, v___x_2937_, v___x_2930_);
                                leanh::lean_dec_ref(v___x_2925_);
                                v_snd_2939_ = leanh::lean_ctor_get(v___x_2938_, 1);
                                leanh::lean_inc(v_snd_2939_);
                                leanh::lean_dec_ref(v___x_2938_);
                                v___y_2851_ = v_snd_2939_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2815_ = leanh::lean_box(0);
                v___x_2816_ = 1;
                v___x_2817_ = leanh::lean_box((v___x_2816_) as usize);
                leanh::lean_inc_n(v___y_2809_, 2);
                v___x_2818_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_2809_, v___x_2817_, v_keyTys_2810_);
                v___x_2819_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
                leanh::lean_inc(v_x_2803_);
                v___x_2820_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2820_, 0, v_x_2803_);
                leanh::lean_ctor_set(v___x_2820_, 1, v___x_2819_);
                v___x_2821_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2821_, 0, v_x_2803_);
                leanh::lean_ctor_set(v___x_2821_, 1, v___y_2809_);
                leanh::lean_ctor_set(v___x_2821_, 2, v___x_2820_);
                v___x_2822_ = lean_array_push(v_items_2814_, v___x_2821_);
                v___x_2823_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_2823_, 0, v___x_2818_);
                leanh::lean_ctor_set(v___x_2823_, 1, v_arrKeyTys_2811_);
                leanh::lean_ctor_set(v___x_2823_, 2, v_arrParents_2812_);
                leanh::lean_ctor_set(v___x_2823_, 3, v_currArrKey_2813_);
                leanh::lean_ctor_set(v___x_2823_, 4, v___y_2809_);
                leanh::lean_ctor_set(v___x_2823_, 5, v___x_2822_);
                v___x_2824_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2824_, 0, v___x_2815_);
                leanh::lean_ctor_set(v___x_2824_, 1, v___x_2823_);
                v___x_2825_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2825_, 0, v___x_2824_);
                return v___x_2825_;
            }
            2 => {
                v_sz_2852_ = lean_array_size(v___y_2851_);
                v___x_2853_ = 0usize;
                v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_2852_, v___x_2853_, v___y_2851_);
                if leanh::lean_obj_tag(v___x_2854_) == 0 {
                    leanh::lean_dec(v_x_2803_);
                    v___x_2855_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                    v___x_2856_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2849_, v___x_2855_, v_a_2804_, v___x_2845_, v_a_2806_);
                    leanh::lean_dec_ref_known(v___x_2845_, 14);
                    leanh::lean_dec_ref(v_a_2804_);
                    leanh::lean_dec(v___x_2849_);
                    return v___x_2856_;
                } else {
                    leanh::lean_dec(v___x_2849_);
                    v_val_2857_ = leanh::lean_ctor_get(v___x_2854_, 0);
                    leanh::lean_inc(v_val_2857_);
                    leanh::lean_dec_ref_known(v___x_2854_, 1);
                    v___x_2858_ = leanh::lean_box(0);
                    v___x_2859_ = lean_array_get_size(v_val_2857_);
                    v___x_2860_ = lean_nat_sub(v___x_2859_, v___x_2848_);
                    v_tailKey_2861_ = lean_array_get(v___x_2858_, v_val_2857_, v___x_2860_);
                    leanh::lean_dec(v___x_2860_);
                    v___x_2862_ = lean_array_pop(v_val_2857_);
                    v___x_2863_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(
                        v___x_2862_,
                        v_a_2804_,
                        v___x_2845_,
                        v_a_2806_,
                    );
                    leanh::lean_dec_ref(v___x_2862_);
                    if leanh::lean_obj_tag(v___x_2863_) == 0 {
                        v_a_2864_ = leanh::lean_ctor_get(v___x_2863_, 0);
                        leanh::lean_inc(v_a_2864_);
                        leanh::lean_dec_ref_known(v___x_2863_, 1);
                        v_fst_2865_ = leanh::lean_ctor_get(v_a_2864_, 0);
                        v_snd_2866_ = leanh::lean_ctor_get(v_a_2864_, 1);
                        v_isSharedCheck_2910_ = (!leanh::lean_is_exclusive(v_a_2864_)) as u8;
                        if v_isSharedCheck_2910_ == 0 {
                            v___x_2868_ = v_a_2864_;
                            v_isShared_2869_ = v_isSharedCheck_2910_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_2866_);
                            leanh::lean_inc(v_fst_2865_);
                            leanh::lean_dec(v_a_2864_);
                            v___x_2868_ = leanh::lean_box(0);
                            v_isShared_2869_ = v_isSharedCheck_2910_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_tailKey_2861_);
                        leanh::lean_dec_ref_known(v___x_2845_, 14);
                        leanh::lean_dec(v_x_2803_);
                        v_a_2911_ = leanh::lean_ctor_get(v___x_2863_, 0);
                        v_isSharedCheck_2918_ =
                            (!leanh::lean_is_exclusive(v___x_2863_)) as u8;
                        if v_isSharedCheck_2918_ == 0 {
                            v___x_2913_ = v___x_2863_;
                            v_isShared_2914_ = v_isSharedCheck_2918_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2911_);
                            leanh::lean_dec(v___x_2863_);
                            v___x_2913_ = leanh::lean_box(0);
                            v_isShared_2914_ = v_isSharedCheck_2918_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_tailKey_2861_);
                v___x_2870_ = l_Lake_Toml_elabSimpleKey(v_tailKey_2861_, v___x_2845_, v_a_2806_);
                if leanh::lean_obj_tag(v___x_2870_) == 0 {
                    v_a_2871_ = leanh::lean_ctor_get(v___x_2870_, 0);
                    leanh::lean_inc(v_a_2871_);
                    leanh::lean_dec_ref_known(v___x_2870_, 1);
                    v_keyTys_2872_ = leanh::lean_ctor_get(v_snd_2866_, 0);
                    v_arrKeyTys_2873_ = leanh::lean_ctor_get(v_snd_2866_, 1);
                    v_arrParents_2874_ = leanh::lean_ctor_get(v_snd_2866_, 2);
                    v_currArrKey_2875_ = leanh::lean_ctor_get(v_snd_2866_, 3);
                    v_items_2876_ = leanh::lean_ctor_get(v_snd_2866_, 5);
                    v___x_2877_ = l_Lean_Name_str___override(v_fst_2865_, v_a_2871_);
                    v___x_2878_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_2872_, v___x_2877_);
                    if leanh::lean_obj_tag(v___x_2878_) == 1 {
                        v_val_2879_ = leanh::lean_ctor_get(v___x_2878_, 0);
                        v_isSharedCheck_2901_ =
                            (!leanh::lean_is_exclusive(v___x_2878_)) as u8;
                        if v_isSharedCheck_2901_ == 0 {
                            v___x_2881_ = v___x_2878_;
                            v_isShared_2882_ = v_isSharedCheck_2901_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2879_);
                            leanh::lean_dec(v___x_2878_);
                            v___x_2881_ = leanh::lean_box(0);
                            v_isShared_2882_ = v_isSharedCheck_2901_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_inc_ref(v_items_2876_);
                        leanh::lean_inc(v_currArrKey_2875_);
                        leanh::lean_inc(v_arrParents_2874_);
                        leanh::lean_inc(v_arrKeyTys_2873_);
                        leanh::lean_inc(v_keyTys_2872_);
                        leanh::lean_dec(v___x_2878_);
                        leanh::lean_del_object(v___x_2868_);
                        leanh::lean_dec(v_snd_2866_);
                        leanh::lean_dec(v_tailKey_2861_);
                        leanh::lean_dec_ref_known(v___x_2845_, 14);
                        v___y_2809_ = v___x_2877_;
                        v_keyTys_2810_ = v_keyTys_2872_;
                        v_arrKeyTys_2811_ = v_arrKeyTys_2873_;
                        v_arrParents_2812_ = v_arrParents_2874_;
                        v_currArrKey_2813_ = v_currArrKey_2875_;
                        v_items_2814_ = v_items_2876_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2868_);
                    leanh::lean_dec(v_snd_2866_);
                    leanh::lean_dec(v_fst_2865_);
                    leanh::lean_dec(v_tailKey_2861_);
                    leanh::lean_dec_ref_known(v___x_2845_, 14);
                    leanh::lean_dec(v_x_2803_);
                    v_a_2902_ = leanh::lean_ctor_get(v___x_2870_, 0);
                    v_isSharedCheck_2909_ = (!leanh::lean_is_exclusive(v___x_2870_)) as u8;
                    if v_isSharedCheck_2909_ == 0 {
                        v___x_2904_ = v___x_2870_;
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2902_);
                        leanh::lean_dec(v___x_2870_);
                        v___x_2904_ = leanh::lean_box(0);
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2883_ = (leanh::lean_unbox(v_val_2879_) as u8);
                if v___x_2883_ == 4 {
                    leanh::lean_inc_ref(v_items_2876_);
                    leanh::lean_inc(v_currArrKey_2875_);
                    leanh::lean_inc(v_arrParents_2874_);
                    leanh::lean_inc(v_arrKeyTys_2873_);
                    leanh::lean_inc(v_keyTys_2872_);
                    leanh::lean_del_object(v___x_2881_);
                    leanh::lean_dec(v_val_2879_);
                    leanh::lean_del_object(v___x_2868_);
                    leanh::lean_dec(v_snd_2866_);
                    leanh::lean_dec(v_tailKey_2861_);
                    leanh::lean_dec_ref_known(v___x_2845_, 14);
                    v___y_2809_ = v___x_2877_;
                    v_keyTys_2810_ = v_keyTys_2872_;
                    v_arrKeyTys_2811_ = v_arrKeyTys_2873_;
                    v_arrParents_2812_ = v_arrParents_2874_;
                    v_currArrKey_2813_ = v_currArrKey_2875_;
                    v_items_2814_ = v_items_2876_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_x_2803_);
                    v___x_2884_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
                    v___x_2885_ = (leanh::lean_unbox(v_val_2879_) as u8);
                    leanh::lean_dec(v_val_2879_);
                    v___x_2886_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(
                        v___x_2885_,
                    );
                    if v_isShared_2882_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2881_, 3);
                        leanh::lean_ctor_set(v___x_2881_, 0, v___x_2886_);
                        v___x_2888_ = v___x_2881_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2900_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2886_);
                        v___x_2888_ = v_reuseFailAlloc_2900_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2889_ = l_Lean_MessageData_ofFormat(v___x_2888_);
                if v_isShared_2869_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2868_, 7);
                    leanh::lean_ctor_set(v___x_2868_, 1, v___x_2889_);
                    leanh::lean_ctor_set(v___x_2868_, 0, v___x_2884_);
                    v___x_2891_ = v___x_2868_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2899_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2889_);
                    v___x_2891_ = v_reuseFailAlloc_2899_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2892_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
                v___x_2893_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2893_, 0, v___x_2891_);
                leanh::lean_ctor_set(v___x_2893_, 1, v___x_2892_);
                v___x_2894_ = l_Lean_MessageData_ofName(v___x_2877_);
                v___x_2895_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2895_, 0, v___x_2893_);
                leanh::lean_ctor_set(v___x_2895_, 1, v___x_2894_);
                v___x_2896_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                v___x_2897_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2897_, 0, v___x_2895_);
                leanh::lean_ctor_set(v___x_2897_, 1, v___x_2896_);
                v___x_2898_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_2861_, v___x_2897_, v_snd_2866_, v___x_2845_, v_a_2806_);
                leanh::lean_dec_ref_known(v___x_2845_, 14);
                leanh::lean_dec(v_snd_2866_);
                leanh::lean_dec(v_tailKey_2861_);
                return v___x_2898_;
            }
            7 => {
                if v_isShared_2905_ == 0 {
                    v___x_2907_ = v___x_2904_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2908_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
                    v___x_2907_ = v_reuseFailAlloc_2908_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2907_;
            }
            9 => {
                if v_isShared_2914_ == 0 {
                    v___x_2916_ = v___x_2913_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2917_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
                    v___x_2916_ = v_reuseFailAlloc_2917_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(
    mut v_x_2940_: *mut leanh::LeanObject,
    mut v_a_2941_: *mut leanh::LeanObject,
    mut v_a_2942_: *mut leanh::LeanObject,
    mut v_a_2943_: *mut leanh::LeanObject,
    mut v_a_2944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2945_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(
        v_x_2940_, v_a_2941_, v_a_2942_, v_a_2943_,
    );
    leanh::lean_dec(v_a_2943_);
    leanh::lean_dec_ref(v_a_2942_);
    return v_res_2945_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2952_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2;
    v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
    return v___x_2953_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(
    mut v_x_2954_: *mut leanh::LeanObject,
    mut v_a_2955_: *mut leanh::LeanObject,
    mut v_a_2956_: *mut leanh::LeanObject,
    mut v_a_2957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2971_: u8 = 0;
    let mut v_cancelTk_x3f_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2973_: u8 = 0;
    let mut v_inheritedTraceOptions_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: u8 = 0;
    let mut v_ref_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: u8 = 0;
    let mut v___y_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2995_: usize = 0;
    let mut v___x_2996_: usize = 0;
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tailKey_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3013_: u8 = 0;
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v_keyTys_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrParents_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3029_: u8 = 0;
    let mut v___x_3030_: u8 = 0;
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut v_unused_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3080_: u8 = 0;
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: u8 = 0;
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3103_: u8 = 0;
    let mut v_unused_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3110_: u8 = 0;
    let mut v_a_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3114_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3118_: u8 = 0;
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v_a_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: u8 = 0;
    let mut v___x_3139_: usize = 0;
    let mut v___x_3140_: usize = 0;
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: usize = 0;
    let mut v___x_3144_: usize = 0;
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2959_ = leanh::lean_ctor_get(v_a_2956_, 0);
                v_fileMap_2960_ = leanh::lean_ctor_get(v_a_2956_, 1);
                v_options_2961_ = leanh::lean_ctor_get(v_a_2956_, 2);
                v_currRecDepth_2962_ = leanh::lean_ctor_get(v_a_2956_, 3);
                v_maxRecDepth_2963_ = leanh::lean_ctor_get(v_a_2956_, 4);
                v_ref_2964_ = leanh::lean_ctor_get(v_a_2956_, 5);
                v_currNamespace_2965_ = leanh::lean_ctor_get(v_a_2956_, 6);
                v_openDecls_2966_ = leanh::lean_ctor_get(v_a_2956_, 7);
                v_initHeartbeats_2967_ = leanh::lean_ctor_get(v_a_2956_, 8);
                v_maxHeartbeats_2968_ = leanh::lean_ctor_get(v_a_2956_, 9);
                v_quotContext_2969_ = leanh::lean_ctor_get(v_a_2956_, 10);
                v_currMacroScope_2970_ = leanh::lean_ctor_get(v_a_2956_, 11);
                v_diag_2971_ = leanh::lean_ctor_get_uint8(
                    v_a_2956_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2972_ = leanh::lean_ctor_get(v_a_2956_, 12);
                v_suppressElabErrors_2973_ = leanh::lean_ctor_get_uint8(
                    v_a_2956_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2974_ = leanh::lean_ctor_get(v_a_2956_, 13);
                v___x_2975_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1;
                leanh::lean_inc(v_x_2954_);
                v___x_2976_ = l_Lean_Syntax_isOfKind(v_x_2954_, v___x_2975_);
                v_ref_2977_ = l_Lean_replaceRef(v_x_2954_, v_ref_2964_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_2974_);
                leanh::lean_inc(v_cancelTk_x3f_2972_);
                leanh::lean_inc(v_currMacroScope_2970_);
                leanh::lean_inc(v_quotContext_2969_);
                leanh::lean_inc(v_maxHeartbeats_2968_);
                leanh::lean_inc(v_initHeartbeats_2967_);
                leanh::lean_inc(v_openDecls_2966_);
                leanh::lean_inc(v_currNamespace_2965_);
                leanh::lean_inc(v_maxRecDepth_2963_);
                leanh::lean_inc(v_currRecDepth_2962_);
                leanh::lean_inc_ref(v_options_2961_);
                leanh::lean_inc_ref(v_fileMap_2960_);
                leanh::lean_inc_ref(v_fileName_2959_);
                v___x_2978_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2978_, 0, v_fileName_2959_);
                leanh::lean_ctor_set(v___x_2978_, 1, v_fileMap_2960_);
                leanh::lean_ctor_set(v___x_2978_, 2, v_options_2961_);
                leanh::lean_ctor_set(v___x_2978_, 3, v_currRecDepth_2962_);
                leanh::lean_ctor_set(v___x_2978_, 4, v_maxRecDepth_2963_);
                leanh::lean_ctor_set(v___x_2978_, 5, v_ref_2977_);
                leanh::lean_ctor_set(v___x_2978_, 6, v_currNamespace_2965_);
                leanh::lean_ctor_set(v___x_2978_, 7, v_openDecls_2966_);
                leanh::lean_ctor_set(v___x_2978_, 8, v_initHeartbeats_2967_);
                leanh::lean_ctor_set(v___x_2978_, 9, v_maxHeartbeats_2968_);
                leanh::lean_ctor_set(v___x_2978_, 10, v_quotContext_2969_);
                leanh::lean_ctor_set(v___x_2978_, 11, v_currMacroScope_2970_);
                leanh::lean_ctor_set(v___x_2978_, 12, v_cancelTk_x3f_2972_);
                leanh::lean_ctor_set(v___x_2978_, 13, v_inheritedTraceOptions_2974_);
                leanh::lean_ctor_set_uint8(
                    v___x_2978_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_2971_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2978_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2973_,
                );
                if v___x_2976_ == 0 {
                    v___x_2987_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
                    v___x_2988_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_2954_, v___x_2987_, v_a_2955_, v___x_2978_, v_a_2957_);
                    leanh::lean_dec_ref_known(v___x_2978_, 14);
                    leanh::lean_dec_ref(v_a_2955_);
                    leanh::lean_dec(v_x_2954_);
                    return v___x_2988_;
                } else {
                    v___x_2989_ = leanh::lean_unsigned_to_nat(2);
                    v___x_2990_ = l_Lean_Syntax_getArg(v_x_2954_, v___x_2989_);
                    v___x_2991_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5;
                    leanh::lean_inc(v___x_2990_);
                    v___x_2992_ = l_Lean_Syntax_isOfKind(v___x_2990_, v___x_2991_);
                    if v___x_2992_ == 0 {
                        leanh::lean_dec(v___x_2990_);
                        v___x_3128_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                        v___x_3129_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_2954_, v___x_3128_, v_a_2955_, v___x_2978_, v_a_2957_);
                        leanh::lean_dec_ref_known(v___x_2978_, 14);
                        leanh::lean_dec_ref(v_a_2955_);
                        leanh::lean_dec(v_x_2954_);
                        return v___x_3129_;
                    } else {
                        v___x_3130_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3131_ = l_Lean_Syntax_getArg(v___x_2990_, v___x_3130_);
                        leanh::lean_dec(v___x_2990_);
                        v___x_3132_ = l_Lean_Syntax_getArgs(v___x_3131_);
                        leanh::lean_dec(v___x_3131_);
                        v___x_3133_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8;
                        v___x_3134_ = lean_array_get_size(v___x_3132_);
                        v___x_3135_ = lean_nat_dec_lt(v___x_3130_, v___x_3134_);
                        if v___x_3135_ == 0 {
                            leanh::lean_dec_ref(v___x_3132_);
                            v___y_2994_ = v___x_3133_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3136_ = leanh::lean_box((v___x_2992_) as usize);
                            v___x_3137_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3137_, 0, v___x_3136_);
                            leanh::lean_ctor_set(v___x_3137_, 1, v___x_3133_);
                            v___x_3138_ = lean_nat_dec_le(v___x_3134_, v___x_3134_);
                            if v___x_3138_ == 0 {
                                if v___x_3135_ == 0 {
                                    leanh::lean_dec_ref_known(v___x_3137_, 2);
                                    leanh::lean_dec_ref(v___x_3132_);
                                    v___y_2994_ = v___x_3133_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3139_ = 0usize;
                                    v___x_3140_ = lean_usize_of_nat(v___x_3134_);
                                    v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2992_, v___x_3132_, v___x_3139_, v___x_3140_, v___x_3137_);
                                    leanh::lean_dec_ref(v___x_3132_);
                                    v_snd_3142_ = leanh::lean_ctor_get(v___x_3141_, 1);
                                    leanh::lean_inc(v_snd_3142_);
                                    leanh::lean_dec_ref(v___x_3141_);
                                    v___y_2994_ = v_snd_3142_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_3143_ = 0usize;
                                v___x_3144_ = lean_usize_of_nat(v___x_3134_);
                                v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2992_, v___x_3132_, v___x_3143_, v___x_3144_, v___x_3137_);
                                leanh::lean_dec_ref(v___x_3132_);
                                v_snd_3146_ = leanh::lean_ctor_get(v___x_3145_, 1);
                                leanh::lean_inc(v_snd_3146_);
                                leanh::lean_dec_ref(v___x_3145_);
                                v___y_2994_ = v_snd_3146_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2981_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
                v___x_2982_ = l_Lean_MessageData_ofName(v___y_2980_);
                v___x_2983_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2983_, 0, v___x_2981_);
                leanh::lean_ctor_set(v___x_2983_, 1, v___x_2982_);
                v___x_2984_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                v___x_2985_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2985_, 0, v___x_2983_);
                leanh::lean_ctor_set(v___x_2985_, 1, v___x_2984_);
                v___x_2986_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_2985_, v___x_2978_, v_a_2957_);
                leanh::lean_dec_ref_known(v___x_2978_, 14);
                return v___x_2986_;
            }
            2 => {
                v_sz_2995_ = lean_array_size(v___y_2994_);
                v___x_2996_ = 0usize;
                v___x_2997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_2995_, v___x_2996_, v___y_2994_);
                if leanh::lean_obj_tag(v___x_2997_) == 0 {
                    v___x_2998_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                    v___x_2999_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_2954_, v___x_2998_, v_a_2955_, v___x_2978_, v_a_2957_);
                    leanh::lean_dec_ref_known(v___x_2978_, 14);
                    leanh::lean_dec_ref(v_a_2955_);
                    leanh::lean_dec(v_x_2954_);
                    return v___x_2999_;
                } else {
                    v_val_3000_ = leanh::lean_ctor_get(v___x_2997_, 0);
                    leanh::lean_inc(v_val_3000_);
                    leanh::lean_dec_ref_known(v___x_2997_, 1);
                    v___x_3001_ = leanh::lean_box(0);
                    v___x_3002_ = lean_array_get_size(v_val_3000_);
                    v___x_3003_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3004_ = lean_nat_sub(v___x_3002_, v___x_3003_);
                    v_tailKey_3005_ = lean_array_get(v___x_3001_, v_val_3000_, v___x_3004_);
                    leanh::lean_dec(v___x_3004_);
                    v___x_3006_ = lean_array_pop(v_val_3000_);
                    v___x_3007_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(
                        v___x_3006_,
                        v_a_2955_,
                        v___x_2978_,
                        v_a_2957_,
                    );
                    leanh::lean_dec_ref(v___x_3006_);
                    if leanh::lean_obj_tag(v___x_3007_) == 0 {
                        v_a_3008_ = leanh::lean_ctor_get(v___x_3007_, 0);
                        leanh::lean_inc(v_a_3008_);
                        leanh::lean_dec_ref_known(v___x_3007_, 1);
                        v_fst_3009_ = leanh::lean_ctor_get(v_a_3008_, 0);
                        v_snd_3010_ = leanh::lean_ctor_get(v_a_3008_, 1);
                        v_isSharedCheck_3119_ = (!leanh::lean_is_exclusive(v_a_3008_)) as u8;
                        if v_isSharedCheck_3119_ == 0 {
                            v___x_3012_ = v_a_3008_;
                            v_isShared_3013_ = v_isSharedCheck_3119_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3010_);
                            leanh::lean_inc(v_fst_3009_);
                            leanh::lean_dec(v_a_3008_);
                            v___x_3012_ = leanh::lean_box(0);
                            v_isShared_3013_ = v_isSharedCheck_3119_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_tailKey_3005_);
                        leanh::lean_dec_ref_known(v___x_2978_, 14);
                        leanh::lean_dec(v_x_2954_);
                        v_a_3120_ = leanh::lean_ctor_get(v___x_3007_, 0);
                        v_isSharedCheck_3127_ =
                            (!leanh::lean_is_exclusive(v___x_3007_)) as u8;
                        if v_isSharedCheck_3127_ == 0 {
                            v___x_3122_ = v___x_3007_;
                            v_isShared_3123_ = v_isSharedCheck_3127_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3120_);
                            leanh::lean_dec(v___x_3007_);
                            v___x_3122_ = leanh::lean_box(0);
                            v_isShared_3123_ = v_isSharedCheck_3127_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_tailKey_3005_);
                v___x_3014_ = l_Lake_Toml_elabSimpleKey(v_tailKey_3005_, v___x_2978_, v_a_2957_);
                if leanh::lean_obj_tag(v___x_3014_) == 0 {
                    v_a_3015_ = leanh::lean_ctor_get(v___x_3014_, 0);
                    v_isSharedCheck_3110_ = (!leanh::lean_is_exclusive(v___x_3014_)) as u8;
                    if v_isSharedCheck_3110_ == 0 {
                        v___x_3017_ = v___x_3014_;
                        v_isShared_3018_ = v_isSharedCheck_3110_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3015_);
                        leanh::lean_dec(v___x_3014_);
                        v___x_3017_ = leanh::lean_box(0);
                        v_isShared_3018_ = v_isSharedCheck_3110_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3012_);
                    leanh::lean_dec(v_snd_3010_);
                    leanh::lean_dec(v_fst_3009_);
                    leanh::lean_dec(v_tailKey_3005_);
                    leanh::lean_dec_ref_known(v___x_2978_, 14);
                    leanh::lean_dec(v_x_2954_);
                    v_a_3111_ = leanh::lean_ctor_get(v___x_3014_, 0);
                    v_isSharedCheck_3118_ = (!leanh::lean_is_exclusive(v___x_3014_)) as u8;
                    if v_isSharedCheck_3118_ == 0 {
                        v___x_3113_ = v___x_3014_;
                        v_isShared_3114_ = v_isSharedCheck_3118_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3111_);
                        leanh::lean_dec(v___x_3014_);
                        v___x_3113_ = leanh::lean_box(0);
                        v_isShared_3114_ = v_isSharedCheck_3118_;
                        state = 15;
                        continue;
                    }
                }
            }
            4 => {
                v_keyTys_3019_ = leanh::lean_ctor_get(v_snd_3010_, 0);
                v_arrKeyTys_3020_ = leanh::lean_ctor_get(v_snd_3010_, 1);
                v_arrParents_3021_ = leanh::lean_ctor_get(v_snd_3010_, 2);
                v_currArrKey_3022_ = leanh::lean_ctor_get(v_snd_3010_, 3);
                v_items_3023_ = leanh::lean_ctor_get(v_snd_3010_, 5);
                v___x_3024_ = l_Lean_Name_str___override(v_fst_3009_, v_a_3015_);
                v___x_3025_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_3019_, v___x_3024_);
                if leanh::lean_obj_tag(v___x_3025_) == 1 {
                    v_val_3026_ = leanh::lean_ctor_get(v___x_3025_, 0);
                    v_isSharedCheck_3077_ = (!leanh::lean_is_exclusive(v___x_3025_)) as u8;
                    if v_isSharedCheck_3077_ == 0 {
                        v___x_3028_ = v___x_3025_;
                        v_isShared_3029_ = v_isSharedCheck_3077_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3026_);
                        leanh::lean_dec(v___x_3025_);
                        v___x_3028_ = leanh::lean_box(0);
                        v_isShared_3029_ = v_isSharedCheck_3077_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_items_3023_);
                    leanh::lean_inc(v_currArrKey_3022_);
                    leanh::lean_inc(v_arrParents_3021_);
                    leanh::lean_inc(v_arrKeyTys_3020_);
                    leanh::lean_inc(v_keyTys_3019_);
                    leanh::lean_dec(v___x_3025_);
                    leanh::lean_dec(v_tailKey_3005_);
                    leanh::lean_dec_ref_known(v___x_2978_, 14);
                    v_isSharedCheck_3103_ = (!leanh::lean_is_exclusive(v_snd_3010_)) as u8;
                    if v_isSharedCheck_3103_ == 0 {
                        v_unused_3104_ = leanh::lean_ctor_get(v_snd_3010_, 5);
                        leanh::lean_dec(v_unused_3104_);
                        v_unused_3105_ = leanh::lean_ctor_get(v_snd_3010_, 4);
                        leanh::lean_dec(v_unused_3105_);
                        v_unused_3106_ = leanh::lean_ctor_get(v_snd_3010_, 3);
                        leanh::lean_dec(v_unused_3106_);
                        v_unused_3107_ = leanh::lean_ctor_get(v_snd_3010_, 2);
                        leanh::lean_dec(v_unused_3107_);
                        v_unused_3108_ = leanh::lean_ctor_get(v_snd_3010_, 1);
                        leanh::lean_dec(v_unused_3108_);
                        v_unused_3109_ = leanh::lean_ctor_get(v_snd_3010_, 0);
                        leanh::lean_dec(v_unused_3109_);
                        v___x_3079_ = v_snd_3010_;
                        v_isShared_3080_ = v_isSharedCheck_3103_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_3010_);
                        v___x_3079_ = leanh::lean_box(0);
                        v_isShared_3080_ = v_isSharedCheck_3103_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3030_ = (leanh::lean_unbox(v_val_3026_) as u8);
                if v___x_3030_ == 2 {
                    leanh::lean_inc_ref(v_items_3023_);
                    leanh::lean_inc(v_arrParents_3021_);
                    leanh::lean_inc(v_arrKeyTys_3020_);
                    leanh::lean_del_object(v___x_3028_);
                    leanh::lean_dec(v_val_3026_);
                    leanh::lean_dec(v_tailKey_3005_);
                    v_isSharedCheck_3055_ = (!leanh::lean_is_exclusive(v_snd_3010_)) as u8;
                    if v_isSharedCheck_3055_ == 0 {
                        v_unused_3056_ = leanh::lean_ctor_get(v_snd_3010_, 5);
                        leanh::lean_dec(v_unused_3056_);
                        v_unused_3057_ = leanh::lean_ctor_get(v_snd_3010_, 4);
                        leanh::lean_dec(v_unused_3057_);
                        v_unused_3058_ = leanh::lean_ctor_get(v_snd_3010_, 3);
                        leanh::lean_dec(v_unused_3058_);
                        v_unused_3059_ = leanh::lean_ctor_get(v_snd_3010_, 2);
                        leanh::lean_dec(v_unused_3059_);
                        v_unused_3060_ = leanh::lean_ctor_get(v_snd_3010_, 1);
                        leanh::lean_dec(v_unused_3060_);
                        v_unused_3061_ = leanh::lean_ctor_get(v_snd_3010_, 0);
                        leanh::lean_dec(v_unused_3061_);
                        v___x_3032_ = v_snd_3010_;
                        v_isShared_3033_ = v_isSharedCheck_3055_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_3010_);
                        v___x_3032_ = leanh::lean_box(0);
                        v_isShared_3033_ = v_isSharedCheck_3055_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3017_);
                    leanh::lean_del_object(v___x_3012_);
                    leanh::lean_dec(v_x_2954_);
                    v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0;
                    v___x_3063_ = (leanh::lean_unbox(v_val_3026_) as u8);
                    leanh::lean_dec(v_val_3026_);
                    v___x_3064_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(
                        v___x_3063_,
                    );
                    v___x_3065_ = lean_string_append(v___x_3062_, v___x_3064_);
                    leanh::lean_dec_ref(v___x_3064_);
                    v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2;
                    v___x_3067_ = lean_string_append(v___x_3065_, v___x_3066_);
                    v___x_3068_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___x_3024_,
                        v___x_2992_,
                    );
                    v___x_3069_ = lean_string_append(v___x_3067_, v___x_3068_);
                    leanh::lean_dec_ref(v___x_3068_);
                    v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4;
                    v___x_3071_ = lean_string_append(v___x_3069_, v___x_3070_);
                    if v_isShared_3029_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3028_, 3);
                        leanh::lean_ctor_set(v___x_3028_, 0, v___x_3071_);
                        v___x_3073_ = v___x_3028_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3076_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3071_);
                        v___x_3073_ = v_reuseFailAlloc_3076_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3034_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_3021_, v___x_3024_);
                if leanh::lean_obj_tag(v___x_3034_) == 0 {
                    leanh::lean_del_object(v___x_3032_);
                    leanh::lean_dec_ref(v_items_3023_);
                    leanh::lean_dec(v_arrParents_3021_);
                    leanh::lean_dec(v_arrKeyTys_3020_);
                    leanh::lean_del_object(v___x_3017_);
                    leanh::lean_del_object(v___x_3012_);
                    leanh::lean_dec(v_x_2954_);
                    v___y_2980_ = v___x_3024_;
                    state = 1;
                    continue;
                } else {
                    v_val_3035_ = leanh::lean_ctor_get(v___x_3034_, 0);
                    leanh::lean_inc(v_val_3035_);
                    leanh::lean_dec_ref_known(v___x_3034_, 1);
                    v___x_3036_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_3020_, v_val_3035_);
                    leanh::lean_dec(v_val_3035_);
                    if leanh::lean_obj_tag(v___x_3036_) == 1 {
                        leanh::lean_dec_ref_known(v___x_2978_, 14);
                        v_val_3037_ = leanh::lean_ctor_get(v___x_3036_, 0);
                        leanh::lean_inc(v_val_3037_);
                        leanh::lean_dec_ref_known(v___x_3036_, 1);
                        v___x_3038_ = leanh::lean_box(0);
                        v___x_3039_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
                        leanh::lean_inc_n(v_x_2954_, 2);
                        v___x_3040_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3040_, 0, v_x_2954_);
                        leanh::lean_ctor_set(v___x_3040_, 1, v___x_3039_);
                        v___x_3041_ = lean_mk_empty_array_with_capacity(v___x_3003_);
                        v___x_3042_ = lean_array_push(v___x_3041_, v___x_3040_);
                        v___x_3043_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3043_, 0, v_x_2954_);
                        leanh::lean_ctor_set(v___x_3043_, 1, v___x_3042_);
                        leanh::lean_inc_n(v___x_3024_, 2);
                        v___x_3044_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_3044_, 0, v_x_2954_);
                        leanh::lean_ctor_set(v___x_3044_, 1, v___x_3024_);
                        leanh::lean_ctor_set(v___x_3044_, 2, v___x_3043_);
                        v___x_3045_ = lean_array_push(v_items_3023_, v___x_3044_);
                        if v_isShared_3033_ == 0 {
                            leanh::lean_ctor_set(v___x_3032_, 5, v___x_3045_);
                            leanh::lean_ctor_set(v___x_3032_, 4, v___x_3024_);
                            leanh::lean_ctor_set(v___x_3032_, 3, v___x_3024_);
                            leanh::lean_ctor_set(v___x_3032_, 0, v_val_3037_);
                            v___x_3047_ = v___x_3032_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3054_ =
                                leanh::lean_alloc_ctor(0, 6, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_val_3037_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3054_,
                                1,
                                v_arrKeyTys_3020_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3054_,
                                2,
                                v_arrParents_3021_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 3, v___x_3024_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 4, v___x_3024_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 5, v___x_3045_);
                            v___x_3047_ = v_reuseFailAlloc_3054_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3036_);
                        leanh::lean_del_object(v___x_3032_);
                        leanh::lean_dec_ref(v_items_3023_);
                        leanh::lean_dec(v_arrParents_3021_);
                        leanh::lean_dec(v_arrKeyTys_3020_);
                        leanh::lean_del_object(v___x_3017_);
                        leanh::lean_del_object(v___x_3012_);
                        leanh::lean_dec(v_x_2954_);
                        v___y_2980_ = v___x_3024_;
                        state = 1;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_3013_ == 0 {
                    leanh::lean_ctor_set(v___x_3012_, 1, v___x_3047_);
                    leanh::lean_ctor_set(v___x_3012_, 0, v___x_3038_);
                    v___x_3049_ = v___x_3012_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3053_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_3047_);
                    v___x_3049_ = v_reuseFailAlloc_3053_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3018_ == 0 {
                    leanh::lean_ctor_set(v___x_3017_, 0, v___x_3049_);
                    v___x_3051_ = v___x_3017_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3052_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3049_);
                    v___x_3051_ = v_reuseFailAlloc_3052_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3051_;
            }
            10 => {
                v___x_3074_ = l_Lean_MessageData_ofFormat(v___x_3073_);
                v___x_3075_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_3005_, v___x_3074_, v_snd_3010_, v___x_2978_, v_a_2957_);
                leanh::lean_dec_ref_known(v___x_2978_, 14);
                leanh::lean_dec(v_snd_3010_);
                leanh::lean_dec(v_tailKey_3005_);
                return v___x_3075_;
            }
            11 => {
                v___x_3081_ = leanh::lean_box(0);
                v___x_3082_ = 2;
                v___x_3083_ = leanh::lean_box((v___x_3082_) as usize);
                leanh::lean_inc_n(v___x_3024_, 4);
                v___x_3084_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_3024_, v___x_3083_, v_keyTys_3019_);
                leanh::lean_inc(v___x_3084_);
                leanh::lean_inc(v_currArrKey_3022_);
                v___x_3085_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_3022_, v___x_3084_, v_arrKeyTys_3020_);
                v___x_3086_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_3024_, v_currArrKey_3022_, v_arrParents_3021_);
                v___x_3087_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
                leanh::lean_inc_n(v_x_2954_, 2);
                v___x_3088_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3088_, 0, v_x_2954_);
                leanh::lean_ctor_set(v___x_3088_, 1, v___x_3087_);
                v___x_3089_ = lean_mk_empty_array_with_capacity(v___x_3003_);
                v___x_3090_ = lean_array_push(v___x_3089_, v___x_3088_);
                v___x_3091_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3091_, 0, v_x_2954_);
                leanh::lean_ctor_set(v___x_3091_, 1, v___x_3090_);
                v___x_3092_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3092_, 0, v_x_2954_);
                leanh::lean_ctor_set(v___x_3092_, 1, v___x_3024_);
                leanh::lean_ctor_set(v___x_3092_, 2, v___x_3091_);
                v___x_3093_ = lean_array_push(v_items_3023_, v___x_3092_);
                if v_isShared_3080_ == 0 {
                    leanh::lean_ctor_set(v___x_3079_, 5, v___x_3093_);
                    leanh::lean_ctor_set(v___x_3079_, 4, v___x_3024_);
                    leanh::lean_ctor_set(v___x_3079_, 3, v___x_3024_);
                    leanh::lean_ctor_set(v___x_3079_, 2, v___x_3086_);
                    leanh::lean_ctor_set(v___x_3079_, 1, v___x_3085_);
                    leanh::lean_ctor_set(v___x_3079_, 0, v___x_3084_);
                    v___x_3095_ = v___x_3079_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3102_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_3085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3102_, 2, v___x_3086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3102_, 3, v___x_3024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3102_, 4, v___x_3024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3102_, 5, v___x_3093_);
                    v___x_3095_ = v_reuseFailAlloc_3102_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3013_ == 0 {
                    leanh::lean_ctor_set(v___x_3012_, 1, v___x_3095_);
                    leanh::lean_ctor_set(v___x_3012_, 0, v___x_3081_);
                    v___x_3097_ = v___x_3012_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3101_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3095_);
                    v___x_3097_ = v_reuseFailAlloc_3101_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3018_ == 0 {
                    leanh::lean_ctor_set(v___x_3017_, 0, v___x_3097_);
                    v___x_3099_ = v___x_3017_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3099_;
            }
            15 => {
                if v_isShared_3114_ == 0 {
                    v___x_3116_ = v___x_3113_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3117_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
                    v___x_3116_ = v_reuseFailAlloc_3117_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3116_;
            }
            17 => {
                if v_isShared_3123_ == 0 {
                    v___x_3125_ = v___x_3122_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3126_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
                    v___x_3125_ = v_reuseFailAlloc_3126_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(
    mut v_x_3147_: *mut leanh::LeanObject,
    mut v_a_3148_: *mut leanh::LeanObject,
    mut v_a_3149_: *mut leanh::LeanObject,
    mut v_a_3150_: *mut leanh::LeanObject,
    mut v_a_3151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3152_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(
        v_x_3147_, v_a_3148_, v_a_3149_, v_a_3150_,
    );
    leanh::lean_dec(v_a_3150_);
    leanh::lean_dec_ref(v_a_3149_);
    return v_res_3152_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3154_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0;
    v___x_3155_ = l_Lean_stringToMessageData(v___x_3154_);
    return v___x_3155_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(
    mut v_x_3156_: *mut leanh::LeanObject,
    mut v_a_3157_: *mut leanh::LeanObject,
    mut v_a_3158_: *mut leanh::LeanObject,
    mut v_a_3159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: u8 = 0;
    v___x_3161_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1;
    leanh::lean_inc(v_x_3156_);
    v___x_3162_ = l_Lean_Syntax_isOfKind(v_x_3156_, v___x_3161_);
    if v___x_3162_ == 0 {
        let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3164_: u8 = 0;
        v___x_3163_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3;
        leanh::lean_inc(v_x_3156_);
        v___x_3164_ = l_Lean_Syntax_isOfKind(v_x_3156_, v___x_3163_);
        if v___x_3164_ == 0 {
            let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3166_: u8 = 0;
            v___x_3165_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1;
            leanh::lean_inc(v_x_3156_);
            v___x_3166_ = l_Lean_Syntax_isOfKind(v_x_3156_, v___x_3165_);
            if v___x_3166_ == 0 {
                let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3167_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
                v___x_3168_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_3156_, v___x_3167_, v_a_3157_, v_a_3158_, v_a_3159_);
                leanh::lean_dec_ref(v_a_3157_);
                leanh::lean_dec(v_x_3156_);
                return v___x_3168_;
            } else {
                let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3169_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(
                    v_x_3156_, v_a_3157_, v_a_3158_, v_a_3159_,
                );
                return v___x_3169_;
            }
        } else {
            let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3170_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(
                v_x_3156_, v_a_3157_, v_a_3158_, v_a_3159_,
            );
            return v___x_3170_;
        }
    } else {
        let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3171_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(
            v_x_3156_, v_a_3157_, v_a_3158_, v_a_3159_,
        );
        return v___x_3171_;
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(
    mut v_x_3172_: *mut leanh::LeanObject,
    mut v_a_3173_: *mut leanh::LeanObject,
    mut v_a_3174_: *mut leanh::LeanObject,
    mut v_a_3175_: *mut leanh::LeanObject,
    mut v_a_3176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3177_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(
        v_x_3172_, v_a_3173_, v_a_3174_, v_a_3175_,
    );
    leanh::lean_dec(v_a_3175_);
    leanh::lean_dec_ref(v_a_3174_);
    return v_res_3177_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(
    mut v_ref_3178_: *mut leanh::LeanObject,
    mut v_as_3179_: *mut leanh::LeanObject,
    mut v_i_3180_: usize,
    mut v_stop_3181_: usize,
    mut v_b_3182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: usize = 0;
    let mut v___x_3186_: usize = 0;
    let mut v___x_3188_: u8 = 0;
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3188_ = lean_usize_dec_eq(v_i_3180_, v_stop_3181_);
                if v___x_3188_ == 0 {
                    v___x_3189_ = lean_array_uget_borrowed(v_as_3179_, v_i_3180_);
                    v_fst_3190_ = leanh::lean_ctor_get(v___x_3189_, 0);
                    v_snd_3191_ = leanh::lean_ctor_get(v___x_3189_, 1);
                    leanh::lean_inc(v_fst_3190_);
                    v___x_3192_ = l_Lean_Name_components(v_fst_3190_);
                    if leanh::lean_obj_tag(v___x_3192_) == 0 {
                        v___y_3184_ = v_b_3182_;
                        state = 1;
                        continue;
                    } else {
                        v_head_3193_ = leanh::lean_ctor_get(v___x_3192_, 0);
                        leanh::lean_inc(v_head_3193_);
                        v_tail_3194_ = leanh::lean_ctor_get(v___x_3192_, 1);
                        leanh::lean_inc(v_tail_3194_);
                        leanh::lean_dec_ref_known(v___x_3192_, 2);
                        leanh::lean_inc(v_snd_3191_);
                        leanh::lean_inc(v_ref_3178_);
                        v___x_3195_ =
                            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(
                                v_b_3182_,
                                v_ref_3178_,
                                v_head_3193_,
                                v_tail_3194_,
                                v_snd_3191_,
                            );
                        v___y_3184_ = v___x_3195_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_ref_3178_);
                    return v_b_3182_;
                }
            }
            1 => {
                v___x_3185_ = 1usize;
                v___x_3186_ = lean_usize_add(v_i_3180_, v___x_3185_);
                v_i_3180_ = v___x_3186_;
                v_b_3182_ = v___y_3184_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(
    mut v_sz_3196_: usize,
    mut v_i_3197_: usize,
    mut v_bs_3198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3199_: u8 = 0;
    let mut v_v_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: usize = 0;
    let mut v___x_3205_: usize = 0;
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3199_ = lean_usize_dec_lt(v_i_3197_, v_sz_3196_);
                if v___x_3199_ == 0 {
                    return v_bs_3198_;
                } else {
                    v_v_3200_ = lean_array_uget(v_bs_3198_, v_i_3197_);
                    v___x_3201_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3202_ = lean_array_uset(v_bs_3198_, v_i_3197_, v___x_3201_);
                    v___x_3203_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(
                            v_v_3200_,
                        );
                    v___x_3204_ = 1usize;
                    v___x_3205_ = lean_usize_add(v_i_3197_, v___x_3204_);
                    v___x_3206_ = lean_array_uset(v_bs_x27_3202_, v_i_3197_, v___x_3203_);
                    v_i_3197_ = v___x_3205_;
                    v_bs_3198_ = v___x_3206_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(
    mut v_a_3208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_xs_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3213_: u8 = 0;
    let mut v_items_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: u8 = 0;
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: usize = 0;
    let mut v___x_3227_: usize = 0;
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: usize = 0;
    let mut v___x_3233_: usize = 0;
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3238_: u8 = 0;
    let mut v_ref_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v_sz_3244_: usize = 0;
    let mut v___x_3245_: usize = 0;
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_3208_) {
                6 => {
                    v_xs_3209_ = leanh::lean_ctor_get(v_a_3208_, 1);
                    v_ref_3210_ = leanh::lean_ctor_get(v_a_3208_, 0);
                    v_isSharedCheck_3238_ = (!leanh::lean_is_exclusive(v_a_3208_)) as u8;
                    if v_isSharedCheck_3238_ == 0 {
                        v___x_3212_ = v_a_3208_;
                        v_isShared_3213_ = v_isSharedCheck_3238_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_xs_3209_);
                        leanh::lean_inc(v_ref_3210_);
                        leanh::lean_dec(v_a_3208_);
                        v___x_3212_ = leanh::lean_box(0);
                        v_isShared_3213_ = v_isSharedCheck_3238_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_ref_3239_ = leanh::lean_ctor_get(v_a_3208_, 0);
                    v_xs_3240_ = leanh::lean_ctor_get(v_a_3208_, 1);
                    v_isSharedCheck_3250_ = (!leanh::lean_is_exclusive(v_a_3208_)) as u8;
                    if v_isSharedCheck_3250_ == 0 {
                        v___x_3242_ = v_a_3208_;
                        v_isShared_3243_ = v_isSharedCheck_3250_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_xs_3240_);
                        leanh::lean_inc(v_ref_3239_);
                        leanh::lean_dec(v_a_3208_);
                        v___x_3242_ = leanh::lean_box(0);
                        v_isShared_3243_ = v_isSharedCheck_3250_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    return v_a_3208_;
                }
            },
            1 => {
                v_items_3214_ = leanh::lean_ctor_get(v_xs_3209_, 0);
                leanh::lean_inc_ref(v_items_3214_);
                leanh::lean_dec_ref(v_xs_3209_);
                v___x_3215_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
                v___x_3216_ = leanh::lean_unsigned_to_nat(0);
                v___x_3217_ = lean_array_get_size(v_items_3214_);
                v___x_3218_ = lean_nat_dec_lt(v___x_3216_, v___x_3217_);
                if v___x_3218_ == 0 {
                    leanh::lean_dec_ref(v_items_3214_);
                    if v_isShared_3213_ == 0 {
                        leanh::lean_ctor_set(v___x_3212_, 1, v___x_3215_);
                        v___x_3220_ = v___x_3212_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3221_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_ref_3210_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___x_3215_);
                        v___x_3220_ = v_reuseFailAlloc_3221_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3222_ = lean_nat_dec_le(v___x_3217_, v___x_3217_);
                    if v___x_3222_ == 0 {
                        if v___x_3218_ == 0 {
                            leanh::lean_dec_ref(v_items_3214_);
                            if v_isShared_3213_ == 0 {
                                leanh::lean_ctor_set(v___x_3212_, 1, v___x_3215_);
                                v___x_3224_ = v___x_3212_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3225_ =
                                    leanh::lean_alloc_ctor(6, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_ref_3210_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 1, v___x_3215_);
                                v___x_3224_ = v_reuseFailAlloc_3225_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_3226_ = 0usize;
                            v___x_3227_ = lean_usize_of_nat(v___x_3217_);
                            leanh::lean_inc(v_ref_3210_);
                            v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_3210_, v_items_3214_, v___x_3226_, v___x_3227_, v___x_3215_);
                            leanh::lean_dec_ref(v_items_3214_);
                            if v_isShared_3213_ == 0 {
                                leanh::lean_ctor_set(v___x_3212_, 1, v___x_3228_);
                                v___x_3230_ = v___x_3212_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3231_ =
                                    leanh::lean_alloc_ctor(6, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_ref_3210_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3228_);
                                v___x_3230_ = v_reuseFailAlloc_3231_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_3232_ = 0usize;
                        v___x_3233_ = lean_usize_of_nat(v___x_3217_);
                        leanh::lean_inc(v_ref_3210_);
                        v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_3210_, v_items_3214_, v___x_3232_, v___x_3233_, v___x_3215_);
                        leanh::lean_dec_ref(v_items_3214_);
                        if v_isShared_3213_ == 0 {
                            leanh::lean_ctor_set(v___x_3212_, 1, v___x_3234_);
                            v___x_3236_ = v___x_3212_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3237_ =
                                leanh::lean_alloc_ctor(6, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_ref_3210_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3234_);
                            v___x_3236_ = v_reuseFailAlloc_3237_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3220_;
            }
            3 => {
                return v___x_3224_;
            }
            4 => {
                return v___x_3230_;
            }
            5 => {
                return v___x_3236_;
            }
            6 => {
                v_sz_3244_ = lean_array_size(v_xs_3240_);
                v___x_3245_ = 0usize;
                v___x_3246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_3244_, v___x_3245_, v_xs_3240_);
                if v_isShared_3243_ == 0 {
                    leanh::lean_ctor_set(v___x_3242_, 1, v___x_3246_);
                    v___x_3248_ = v___x_3242_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3249_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_ref_3239_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3249_, 1, v___x_3246_);
                    v___x_3248_ = v_reuseFailAlloc_3249_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3248_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(
    mut v_newV_3251_: *mut leanh::LeanObject,
    mut v___x_3252_: *mut leanh::LeanObject,
    mut v_v_x3f_3253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v_items_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3267_: u8 = 0;
    let mut v_unused_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3278_: u8 = 0;
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3283_: u8 = 0;
    let mut v_unused_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3289_: u8 = 0;
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_v_x3f_3253_) == 1 {
                    v_val_3254_ = leanh::lean_ctor_get(v_v_x3f_3253_, 0);
                    leanh::lean_inc(v_val_3254_);
                    leanh::lean_dec_ref_known(v_v_x3f_3253_, 1);
                    match leanh::lean_obj_tag(v_val_3254_) {
                        6 => {
                            v_ref_3255_ = leanh::lean_ctor_get(v_val_3254_, 0);
                            leanh::lean_inc(v_ref_3255_);
                            v_xs_3256_ = leanh::lean_ctor_get(v_val_3254_, 1);
                            leanh::lean_inc_ref(v_xs_3256_);
                            leanh::lean_dec_ref_known(v_val_3254_, 2);
                            v___x_3257_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_3251_);
                            if leanh::lean_obj_tag(v___x_3257_) == 6 {
                                v_xs_3258_ = leanh::lean_ctor_get(v___x_3257_, 1);
                                v_isSharedCheck_3267_ =
                                    (!leanh::lean_is_exclusive(v___x_3257_)) as u8;
                                if v_isSharedCheck_3267_ == 0 {
                                    v_unused_3268_ = leanh::lean_ctor_get(v___x_3257_, 0);
                                    leanh::lean_dec(v_unused_3268_);
                                    v___x_3260_ = v___x_3257_;
                                    v_isShared_3261_ = v_isSharedCheck_3267_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_xs_3258_);
                                    leanh::lean_dec(v___x_3257_);
                                    v___x_3260_ = leanh::lean_box(0);
                                    v_isShared_3261_ = v_isSharedCheck_3267_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_xs_3256_);
                                leanh::lean_dec(v_ref_3255_);
                                leanh::lean_dec_ref(v___x_3252_);
                                return v___x_3257_;
                            }
                        }
                        5 => {
                            leanh::lean_dec_ref(v___x_3252_);
                            v_ref_3269_ = leanh::lean_ctor_get(v_val_3254_, 0);
                            v_xs_3270_ = leanh::lean_ctor_get(v_val_3254_, 1);
                            v_isSharedCheck_3289_ =
                                (!leanh::lean_is_exclusive(v_val_3254_)) as u8;
                            if v_isSharedCheck_3289_ == 0 {
                                v___x_3272_ = v_val_3254_;
                                v_isShared_3273_ = v_isSharedCheck_3289_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_xs_3270_);
                                leanh::lean_inc(v_ref_3269_);
                                leanh::lean_dec(v_val_3254_);
                                v___x_3272_ = leanh::lean_box(0);
                                v_isShared_3273_ = v_isSharedCheck_3289_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_val_3254_);
                            leanh::lean_dec_ref(v___x_3252_);
                            v___x_3290_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_3251_);
                            return v___x_3290_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_v_x3f_3253_);
                    leanh::lean_dec_ref(v___x_3252_);
                    v___x_3291_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(
                            v_newV_3251_,
                        );
                    return v___x_3291_;
                }
            }
            1 => {
                v_items_3262_ = leanh::lean_ctor_get(v_xs_3258_, 0);
                leanh::lean_inc_ref(v_items_3262_);
                leanh::lean_dec_ref(v_xs_3258_);
                v___x_3263_ =
                    l_Lake_Toml_RBDict_appendArray___redArg(v___x_3252_, v_xs_3256_, v_items_3262_);
                leanh::lean_dec_ref(v_items_3262_);
                if v_isShared_3261_ == 0 {
                    leanh::lean_ctor_set(v___x_3260_, 1, v___x_3263_);
                    leanh::lean_ctor_set(v___x_3260_, 0, v_ref_3255_);
                    v___x_3265_ = v___x_3260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3266_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_ref_3255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3263_);
                    v___x_3265_ = v_reuseFailAlloc_3266_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3265_;
            }
            3 => {
                v___x_3274_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(
                        v_newV_3251_,
                    );
                if leanh::lean_obj_tag(v___x_3274_) == 5 {
                    leanh::lean_del_object(v___x_3272_);
                    v_xs_3275_ = leanh::lean_ctor_get(v___x_3274_, 1);
                    v_isSharedCheck_3283_ = (!leanh::lean_is_exclusive(v___x_3274_)) as u8;
                    if v_isSharedCheck_3283_ == 0 {
                        v_unused_3284_ = leanh::lean_ctor_get(v___x_3274_, 0);
                        leanh::lean_dec(v_unused_3284_);
                        v___x_3277_ = v___x_3274_;
                        v_isShared_3278_ = v_isSharedCheck_3283_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_xs_3275_);
                        leanh::lean_dec(v___x_3274_);
                        v___x_3277_ = leanh::lean_box(0);
                        v_isShared_3278_ = v_isSharedCheck_3283_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_3285_ = lean_array_push(v_xs_3270_, v___x_3274_);
                    if v_isShared_3273_ == 0 {
                        leanh::lean_ctor_set(v___x_3272_, 1, v___x_3285_);
                        v___x_3287_ = v___x_3272_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3288_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_ref_3269_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3288_, 1, v___x_3285_);
                        v___x_3287_ = v_reuseFailAlloc_3288_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3279_ = l_Array_append___redArg(v_xs_3270_, v_xs_3275_);
                leanh::lean_dec_ref(v_xs_3275_);
                if v_isShared_3278_ == 0 {
                    leanh::lean_ctor_set(v___x_3277_, 1, v___x_3279_);
                    leanh::lean_ctor_set(v___x_3277_, 0, v_ref_3269_);
                    v___x_3281_ = v___x_3277_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3282_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_ref_3269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3282_, 1, v___x_3279_);
                    v___x_3281_ = v_reuseFailAlloc_3282_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3281_;
            }
            6 => {
                return v___x_3287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(
    mut v_newV_3292_: *mut leanh::LeanObject,
    mut v_k_3293_: *mut leanh::LeanObject,
    mut v_t_3294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3300_: u8 = 0;
    let mut v_items_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: u8 = 0;
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3316_: u8 = 0;
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3330_: u8 = 0;
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3295_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0;
                leanh::lean_inc_ref(v_t_3294_);
                leanh::lean_inc(v_k_3293_);
                v___x_3296_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_3295_, v_k_3293_, v_t_3294_);
                if leanh::lean_obj_tag(v___x_3296_) == 1 {
                    leanh::lean_dec(v_k_3293_);
                    v_val_3297_ = leanh::lean_ctor_get(v___x_3296_, 0);
                    v_isSharedCheck_3332_ = (!leanh::lean_is_exclusive(v___x_3296_)) as u8;
                    if v_isSharedCheck_3332_ == 0 {
                        v___x_3299_ = v___x_3296_;
                        v_isShared_3300_ = v_isSharedCheck_3332_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3297_);
                        leanh::lean_dec(v___x_3296_);
                        v___x_3299_ = leanh::lean_box(0);
                        v_isShared_3300_ = v_isSharedCheck_3332_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3296_);
                    v___x_3333_ = leanh::lean_box(0);
                    v___x_3334_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_3292_, v___x_3295_, v___x_3333_);
                    v___x_3335_ = l_Lake_Toml_RBDict_push___redArg(
                        v___x_3295_,
                        v_k_3293_,
                        v___x_3334_,
                        v_t_3294_,
                    );
                    return v___x_3335_;
                }
            }
            1 => {
                v_items_3301_ = leanh::lean_ctor_get(v_t_3294_, 0);
                v_indices_3302_ = leanh::lean_ctor_get(v_t_3294_, 1);
                v_isSharedCheck_3331_ = (!leanh::lean_is_exclusive(v_t_3294_)) as u8;
                if v_isSharedCheck_3331_ == 0 {
                    v___x_3304_ = v_t_3294_;
                    v_isShared_3305_ = v_isSharedCheck_3331_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_indices_3302_);
                    leanh::lean_inc(v_items_3301_);
                    leanh::lean_dec(v_t_3294_);
                    v___x_3304_ = leanh::lean_box(0);
                    v_isShared_3305_ = v_isSharedCheck_3331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3306_ = lean_array_get_size(v_items_3301_);
                v___x_3307_ = lean_nat_dec_lt(v_val_3297_, v___x_3306_);
                if v___x_3307_ == 0 {
                    leanh::lean_del_object(v___x_3299_);
                    leanh::lean_dec(v_val_3297_);
                    leanh::lean_dec_ref(v_newV_3292_);
                    if v_isShared_3305_ == 0 {
                        v___x_3309_ = v___x_3304_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3310_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_items_3301_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_indices_3302_);
                        v___x_3309_ = v_reuseFailAlloc_3310_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_v_3311_ = lean_array_fget(v_items_3301_, v_val_3297_);
                    v_fst_3312_ = leanh::lean_ctor_get(v_v_3311_, 0);
                    v_snd_3313_ = leanh::lean_ctor_get(v_v_3311_, 1);
                    v_isSharedCheck_3330_ = (!leanh::lean_is_exclusive(v_v_3311_)) as u8;
                    if v_isSharedCheck_3330_ == 0 {
                        v___x_3315_ = v_v_3311_;
                        v_isShared_3316_ = v_isSharedCheck_3330_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3313_);
                        leanh::lean_inc(v_fst_3312_);
                        leanh::lean_dec(v_v_3311_);
                        v___x_3315_ = leanh::lean_box(0);
                        v_isShared_3316_ = v_isSharedCheck_3330_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3309_;
            }
            4 => {
                v___x_3317_ = leanh::lean_box(0);
                v_xs_x27_3318_ = lean_array_fset(v_items_3301_, v_val_3297_, v___x_3317_);
                if v_isShared_3300_ == 0 {
                    leanh::lean_ctor_set(v___x_3299_, 0, v_snd_3313_);
                    v___x_3320_ = v___x_3299_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3329_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_snd_3313_);
                    v___x_3320_ = v_reuseFailAlloc_3329_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3321_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_3292_, v___x_3295_, v___x_3320_);
                if v_isShared_3316_ == 0 {
                    leanh::lean_ctor_set(v___x_3315_, 1, v___x_3321_);
                    v___x_3323_ = v___x_3315_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3328_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_fst_3312_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3328_, 1, v___x_3321_);
                    v___x_3323_ = v_reuseFailAlloc_3328_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3324_ = lean_array_fset(v_xs_x27_3318_, v_val_3297_, v___x_3323_);
                leanh::lean_dec(v_val_3297_);
                if v_isShared_3305_ == 0 {
                    leanh::lean_ctor_set(v___x_3304_, 0, v___x_3324_);
                    v___x_3326_ = v___x_3304_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_indices_3302_);
                    v___x_3326_ = v_reuseFailAlloc_3327_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(
    mut v_kRef_3336_: *mut leanh::LeanObject,
    mut v_head_3337_: *mut leanh::LeanObject,
    mut v_tail_3338_: *mut leanh::LeanObject,
    mut v_newV_3339_: *mut leanh::LeanObject,
    mut v___x_3340_: *mut leanh::LeanObject,
    mut v_v_x3f_3341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: u8 = 0;
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3351_: u8 = 0;
    let mut v_v_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3365_: u8 = 0;
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3373_: u8 = 0;
    let mut v_unused_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3385_: u8 = 0;
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_v_x3f_3341_) == 1 {
                    v_val_3342_ = leanh::lean_ctor_get(v_v_x3f_3341_, 0);
                    leanh::lean_inc(v_val_3342_);
                    leanh::lean_dec_ref_known(v_v_x3f_3341_, 1);
                    match leanh::lean_obj_tag(v_val_3342_) {
                        5 => {
                            v_ref_3343_ = leanh::lean_ctor_get(v_val_3342_, 0);
                            v_xs_3344_ = leanh::lean_ctor_get(v_val_3342_, 1);
                            v___x_3345_ = lean_array_get_size(v_xs_3344_);
                            v___x_3346_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3347_ = lean_nat_sub(v___x_3345_, v___x_3346_);
                            v___x_3348_ = lean_nat_dec_lt(v___x_3347_, v___x_3345_);
                            if v___x_3348_ == 0 {
                                leanh::lean_dec(v___x_3347_);
                                leanh::lean_dec_ref(v_newV_3339_);
                                leanh::lean_dec(v_tail_3338_);
                                leanh::lean_dec(v_head_3337_);
                                leanh::lean_dec(v_kRef_3336_);
                                return v_val_3342_;
                            } else {
                                leanh::lean_inc_ref(v_xs_3344_);
                                leanh::lean_inc(v_ref_3343_);
                                v_isSharedCheck_3373_ =
                                    (!leanh::lean_is_exclusive(v_val_3342_)) as u8;
                                if v_isSharedCheck_3373_ == 0 {
                                    v_unused_3374_ = leanh::lean_ctor_get(v_val_3342_, 1);
                                    leanh::lean_dec(v_unused_3374_);
                                    v_unused_3375_ = leanh::lean_ctor_get(v_val_3342_, 0);
                                    leanh::lean_dec(v_unused_3375_);
                                    v___x_3350_ = v_val_3342_;
                                    v_isShared_3351_ = v_isSharedCheck_3373_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_val_3342_);
                                    v___x_3350_ = leanh::lean_box(0);
                                    v_isShared_3351_ = v_isSharedCheck_3373_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        6 => {
                            v_ref_3376_ = leanh::lean_ctor_get(v_val_3342_, 0);
                            v_xs_3377_ = leanh::lean_ctor_get(v_val_3342_, 1);
                            v_isSharedCheck_3385_ =
                                (!leanh::lean_is_exclusive(v_val_3342_)) as u8;
                            if v_isSharedCheck_3385_ == 0 {
                                v___x_3379_ = v_val_3342_;
                                v_isShared_3380_ = v_isSharedCheck_3385_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_xs_3377_);
                                leanh::lean_inc(v_ref_3376_);
                                leanh::lean_dec(v_val_3342_);
                                v___x_3379_ = leanh::lean_box(0);
                                v_isShared_3380_ = v_isSharedCheck_3385_;
                                state = 6;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_val_3342_);
                            v___x_3386_ = l_Lake_Toml_RBDict_empty(
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_3340_,
                            );
                            leanh::lean_inc(v_kRef_3336_);
                            v___x_3387_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_3386_, v_kRef_3336_, v_head_3337_, v_tail_3338_, v_newV_3339_);
                            v___x_3388_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3388_, 0, v_kRef_3336_);
                            leanh::lean_ctor_set(v___x_3388_, 1, v___x_3387_);
                            return v___x_3388_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_v_x3f_3341_);
                    v___x_3389_ = l_Lake_Toml_RBDict_empty(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_3340_,
                    );
                    leanh::lean_inc(v_kRef_3336_);
                    v___x_3390_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(
                            v___x_3389_,
                            v_kRef_3336_,
                            v_head_3337_,
                            v_tail_3338_,
                            v_newV_3339_,
                        );
                    v___x_3391_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3391_, 0, v_kRef_3336_);
                    leanh::lean_ctor_set(v___x_3391_, 1, v___x_3390_);
                    return v___x_3391_;
                }
            }
            1 => {
                v_v_3352_ = lean_array_fget(v_xs_3344_, v___x_3347_);
                v___x_3353_ = leanh::lean_box(0);
                v_xs_x27_3354_ = lean_array_fset(v_xs_3344_, v___x_3347_, v___x_3353_);
                if leanh::lean_obj_tag(v_v_3352_) == 6 {
                    v_ref_3361_ = leanh::lean_ctor_get(v_v_3352_, 0);
                    v_xs_3362_ = leanh::lean_ctor_get(v_v_3352_, 1);
                    v_isSharedCheck_3370_ = (!leanh::lean_is_exclusive(v_v_3352_)) as u8;
                    if v_isSharedCheck_3370_ == 0 {
                        v___x_3364_ = v_v_3352_;
                        v_isShared_3365_ = v_isSharedCheck_3370_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_xs_3362_);
                        leanh::lean_inc(v_ref_3361_);
                        leanh::lean_dec(v_v_3352_);
                        v___x_3364_ = leanh::lean_box(0);
                        v_isShared_3365_ = v_isSharedCheck_3370_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_v_3352_);
                    leanh::lean_dec_ref(v_newV_3339_);
                    leanh::lean_dec(v_tail_3338_);
                    leanh::lean_dec(v_head_3337_);
                    v___x_3371_ = l_Lake_Toml_RBDict_empty(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_3340_,
                    );
                    v___x_3372_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3372_, 0, v_kRef_3336_);
                    leanh::lean_ctor_set(v___x_3372_, 1, v___x_3371_);
                    v___y_3356_ = v___x_3372_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3357_ = lean_array_fset(v_xs_x27_3354_, v___x_3347_, v___y_3356_);
                leanh::lean_dec(v___x_3347_);
                if v_isShared_3351_ == 0 {
                    leanh::lean_ctor_set(v___x_3350_, 1, v___x_3357_);
                    v___x_3359_ = v___x_3350_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3360_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_ref_3343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___x_3357_);
                    v___x_3359_ = v_reuseFailAlloc_3360_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3359_;
            }
            4 => {
                v___x_3366_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(
                        v_xs_3362_,
                        v_kRef_3336_,
                        v_head_3337_,
                        v_tail_3338_,
                        v_newV_3339_,
                    );
                if v_isShared_3365_ == 0 {
                    leanh::lean_ctor_set(v___x_3364_, 1, v___x_3366_);
                    v___x_3368_ = v___x_3364_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3369_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_ref_3361_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3366_);
                    v___x_3368_ = v_reuseFailAlloc_3369_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_3356_ = v___x_3368_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3381_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(
                        v_xs_3377_,
                        v_kRef_3336_,
                        v_head_3337_,
                        v_tail_3338_,
                        v_newV_3339_,
                    );
                if v_isShared_3380_ == 0 {
                    leanh::lean_ctor_set(v___x_3379_, 1, v___x_3381_);
                    v___x_3383_ = v___x_3379_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3384_ = leanh::lean_alloc_ctor(6, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_ref_3376_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3384_, 1, v___x_3381_);
                    v___x_3383_ = v_reuseFailAlloc_3384_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(
    mut v_kRef_3392_: *mut leanh::LeanObject,
    mut v_head_3393_: *mut leanh::LeanObject,
    mut v_tail_3394_: *mut leanh::LeanObject,
    mut v_newV_3395_: *mut leanh::LeanObject,
    mut v_k_3396_: *mut leanh::LeanObject,
    mut v_t_3397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v_items_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indices_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3408_: u8 = 0;
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: u8 = 0;
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3419_: u8 = 0;
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3433_: u8 = 0;
    let mut v_isSharedCheck_3434_: u8 = 0;
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3398_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0;
                leanh::lean_inc_ref(v_t_3397_);
                leanh::lean_inc(v_k_3396_);
                v___x_3399_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_3398_, v_k_3396_, v_t_3397_);
                if leanh::lean_obj_tag(v___x_3399_) == 1 {
                    leanh::lean_dec(v_k_3396_);
                    v_val_3400_ = leanh::lean_ctor_get(v___x_3399_, 0);
                    v_isSharedCheck_3435_ = (!leanh::lean_is_exclusive(v___x_3399_)) as u8;
                    if v_isSharedCheck_3435_ == 0 {
                        v___x_3402_ = v___x_3399_;
                        v_isShared_3403_ = v_isSharedCheck_3435_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3400_);
                        leanh::lean_dec(v___x_3399_);
                        v___x_3402_ = leanh::lean_box(0);
                        v_isShared_3403_ = v_isSharedCheck_3435_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3399_);
                    v___x_3436_ = leanh::lean_box(0);
                    v___x_3437_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_3392_, v_head_3393_, v_tail_3394_, v_newV_3395_, v___x_3398_, v___x_3436_);
                    v___x_3438_ = l_Lake_Toml_RBDict_push___redArg(
                        v___x_3398_,
                        v_k_3396_,
                        v___x_3437_,
                        v_t_3397_,
                    );
                    return v___x_3438_;
                }
            }
            1 => {
                v_items_3404_ = leanh::lean_ctor_get(v_t_3397_, 0);
                v_indices_3405_ = leanh::lean_ctor_get(v_t_3397_, 1);
                v_isSharedCheck_3434_ = (!leanh::lean_is_exclusive(v_t_3397_)) as u8;
                if v_isSharedCheck_3434_ == 0 {
                    v___x_3407_ = v_t_3397_;
                    v_isShared_3408_ = v_isSharedCheck_3434_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_indices_3405_);
                    leanh::lean_inc(v_items_3404_);
                    leanh::lean_dec(v_t_3397_);
                    v___x_3407_ = leanh::lean_box(0);
                    v_isShared_3408_ = v_isSharedCheck_3434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3409_ = lean_array_get_size(v_items_3404_);
                v___x_3410_ = lean_nat_dec_lt(v_val_3400_, v___x_3409_);
                if v___x_3410_ == 0 {
                    leanh::lean_del_object(v___x_3402_);
                    leanh::lean_dec(v_val_3400_);
                    leanh::lean_dec_ref(v_newV_3395_);
                    leanh::lean_dec(v_tail_3394_);
                    leanh::lean_dec(v_head_3393_);
                    leanh::lean_dec(v_kRef_3392_);
                    if v_isShared_3408_ == 0 {
                        v___x_3412_ = v___x_3407_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3413_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_items_3404_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_indices_3405_);
                        v___x_3412_ = v_reuseFailAlloc_3413_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_v_3414_ = lean_array_fget(v_items_3404_, v_val_3400_);
                    v_fst_3415_ = leanh::lean_ctor_get(v_v_3414_, 0);
                    v_snd_3416_ = leanh::lean_ctor_get(v_v_3414_, 1);
                    v_isSharedCheck_3433_ = (!leanh::lean_is_exclusive(v_v_3414_)) as u8;
                    if v_isSharedCheck_3433_ == 0 {
                        v___x_3418_ = v_v_3414_;
                        v_isShared_3419_ = v_isSharedCheck_3433_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3416_);
                        leanh::lean_inc(v_fst_3415_);
                        leanh::lean_dec(v_v_3414_);
                        v___x_3418_ = leanh::lean_box(0);
                        v_isShared_3419_ = v_isSharedCheck_3433_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3412_;
            }
            4 => {
                v___x_3420_ = leanh::lean_box(0);
                v_xs_x27_3421_ = lean_array_fset(v_items_3404_, v_val_3400_, v___x_3420_);
                if v_isShared_3403_ == 0 {
                    leanh::lean_ctor_set(v___x_3402_, 0, v_snd_3416_);
                    v___x_3423_ = v___x_3402_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_snd_3416_);
                    v___x_3423_ = v_reuseFailAlloc_3432_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3424_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_3392_, v_head_3393_, v_tail_3394_, v_newV_3395_, v___x_3398_, v___x_3423_);
                if v_isShared_3419_ == 0 {
                    leanh::lean_ctor_set(v___x_3418_, 1, v___x_3424_);
                    v___x_3426_ = v___x_3418_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3431_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_fst_3415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3424_);
                    v___x_3426_ = v_reuseFailAlloc_3431_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3427_ = lean_array_fset(v_xs_x27_3421_, v_val_3400_, v___x_3426_);
                leanh::lean_dec(v_val_3400_);
                if v_isShared_3408_ == 0 {
                    leanh::lean_ctor_set(v___x_3407_, 0, v___x_3427_);
                    v___x_3429_ = v___x_3407_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3430_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_indices_3405_);
                    v___x_3429_ = v_reuseFailAlloc_3430_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(
    mut v_t_3439_: *mut leanh::LeanObject,
    mut v_kRef_3440_: *mut leanh::LeanObject,
    mut v_k_3441_: *mut leanh::LeanObject,
    mut v_ks_3442_: *mut leanh::LeanObject,
    mut v_newV_3443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_ks_3442_) == 0 {
        let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_kRef_3440_);
        v___x_3444_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_3443_, v_k_3441_, v_t_3439_);
        return v___x_3444_;
    } else {
        let mut v_head_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_3445_ = leanh::lean_ctor_get(v_ks_3442_, 0);
        leanh::lean_inc(v_head_3445_);
        v_tail_3446_ = leanh::lean_ctor_get(v_ks_3442_, 1);
        leanh::lean_inc(v_tail_3446_);
        leanh::lean_dec_ref_known(v_ks_3442_, 2);
        v___x_3447_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_3440_, v_head_3445_, v_tail_3446_, v_newV_3443_, v_k_3441_, v_t_3439_);
        return v___x_3447_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(
    mut v_sz_3448_: *mut leanh::LeanObject,
    mut v_i_3449_: *mut leanh::LeanObject,
    mut v_bs_3450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3451_: usize = 0;
    let mut v_i_boxed_3452_: usize = 0;
    let mut v_res_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3451_ = leanh::lean_unbox_usize(v_sz_3448_);
    leanh::lean_dec(v_sz_3448_);
    v_i_boxed_3452_ = leanh::lean_unbox_usize(v_i_3449_);
    leanh::lean_dec(v_i_3449_);
    v_res_3453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_3451_, v_i_boxed_3452_, v_bs_3450_);
    return v_res_3453_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(
    mut v_ref_3454_: *mut leanh::LeanObject,
    mut v_as_3455_: *mut leanh::LeanObject,
    mut v_i_3456_: *mut leanh::LeanObject,
    mut v_stop_3457_: *mut leanh::LeanObject,
    mut v_b_3458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3459_: usize = 0;
    let mut v_stop_boxed_3460_: usize = 0;
    let mut v_res_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3459_ = leanh::lean_unbox_usize(v_i_3456_);
    leanh::lean_dec(v_i_3456_);
    v_stop_boxed_3460_ = leanh::lean_unbox_usize(v_stop_3457_);
    leanh::lean_dec(v_stop_3457_);
    v_res_3461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_3454_, v_as_3455_, v_i_boxed_3459_, v_stop_boxed_3460_, v_b_3458_);
    leanh::lean_dec_ref(v_as_3455_);
    return v_res_3461_;
}
pub unsafe fn l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0___boxed(
    mut v_kRef_3462_: *mut leanh::LeanObject,
    mut v_head_3463_: *mut leanh::LeanObject,
    mut v_tail_3464_: *mut leanh::LeanObject,
    mut v_newV_3465_: *mut leanh::LeanObject,
    mut v___x_3466_: *mut leanh::LeanObject,
    mut v_v_x3f_3467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_3462_, v_head_3463_, v_tail_3464_, v_newV_3465_, v___x_3466_, v_v_x3f_3467_);
    leanh::lean_dec_ref(v___x_3466_);
    return v_res_3468_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(
    mut v_as_3469_: *mut leanh::LeanObject,
    mut v_i_3470_: usize,
    mut v_stop_3471_: usize,
    mut v_b_3472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: usize = 0;
    let mut v___x_3476_: usize = 0;
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3478_ = lean_usize_dec_eq(v_i_3470_, v_stop_3471_);
                if v___x_3478_ == 0 {
                    v___x_3479_ = lean_array_uget_borrowed(v_as_3469_, v_i_3470_);
                    v_ref_3480_ = leanh::lean_ctor_get(v___x_3479_, 0);
                    v_key_3481_ = leanh::lean_ctor_get(v___x_3479_, 1);
                    v_val_3482_ = leanh::lean_ctor_get(v___x_3479_, 2);
                    leanh::lean_inc(v_key_3481_);
                    v___x_3483_ = l_Lean_Name_components(v_key_3481_);
                    if leanh::lean_obj_tag(v___x_3483_) == 0 {
                        v___y_3474_ = v_b_3472_;
                        state = 1;
                        continue;
                    } else {
                        v_head_3484_ = leanh::lean_ctor_get(v___x_3483_, 0);
                        leanh::lean_inc(v_head_3484_);
                        v_tail_3485_ = leanh::lean_ctor_get(v___x_3483_, 1);
                        leanh::lean_inc(v_tail_3485_);
                        leanh::lean_dec_ref_known(v___x_3483_, 2);
                        leanh::lean_inc_ref(v_val_3482_);
                        leanh::lean_inc(v_ref_3480_);
                        v___x_3486_ =
                            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(
                                v_b_3472_,
                                v_ref_3480_,
                                v_head_3484_,
                                v_tail_3485_,
                                v_val_3482_,
                            );
                        v___y_3474_ = v___x_3486_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3472_;
                }
            }
            1 => {
                v___x_3475_ = 1usize;
                v___x_3476_ = lean_usize_add(v_i_3470_, v___x_3475_);
                v_i_3470_ = v___x_3476_;
                v_b_3472_ = v___y_3474_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(
    mut v_as_3487_: *mut leanh::LeanObject,
    mut v_i_3488_: *mut leanh::LeanObject,
    mut v_stop_3489_: *mut leanh::LeanObject,
    mut v_b_3490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3491_: usize = 0;
    let mut v_stop_boxed_3492_: usize = 0;
    let mut v_res_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3491_ = leanh::lean_unbox_usize(v_i_3488_);
    leanh::lean_dec(v_i_3488_);
    v_stop_boxed_3492_ = leanh::lean_unbox_usize(v_stop_3489_);
    leanh::lean_dec(v_stop_3489_);
    v_res_3493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_3487_, v_i_boxed_3491_, v_stop_boxed_3492_, v_b_3490_);
    leanh::lean_dec_ref(v_as_3487_);
    return v_res_3493_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(
    mut v_items_3494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    v___x_3495_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once
        ),
        _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1,
    );
    v___x_3496_ = leanh::lean_unsigned_to_nat(0);
    v___x_3497_ = lean_array_get_size(v_items_3494_);
    v___x_3498_ = lean_nat_dec_lt(v___x_3496_, v___x_3497_);
    if v___x_3498_ == 0 {
        return v___x_3495_;
    } else {
        let mut v___x_3499_: u8 = 0;
        v___x_3499_ = lean_nat_dec_le(v___x_3497_, v___x_3497_);
        if v___x_3499_ == 0 {
            if v___x_3498_ == 0 {
                return v___x_3495_;
            } else {
                let mut v___x_3500_: usize = 0;
                let mut v___x_3501_: usize = 0;
                let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3500_ = 0usize;
                v___x_3501_ = lean_usize_of_nat(v___x_3497_);
                v___x_3502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_3494_, v___x_3500_, v___x_3501_, v___x_3495_);
                return v___x_3502_;
            }
        } else {
            let mut v___x_3503_: usize = 0;
            let mut v___x_3504_: usize = 0;
            let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3503_ = 0usize;
            v___x_3504_ = lean_usize_of_nat(v___x_3497_);
            v___x_3505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_3494_, v___x_3503_, v___x_3504_, v___x_3495_);
            return v___x_3505_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(
    mut v_items_3506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3507_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_3506_);
    leanh::lean_dec_ref(v_items_3506_);
    return v_res_3507_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(
    mut v_x_3508_: *mut leanh::LeanObject,
    mut v_a_3509_: *mut leanh::LeanObject,
    mut v_a_3510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3517_: u8 = 0;
    let mut v_snd_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_a_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3532_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3512_ = l_Lake_Toml_instInhabitedElabState_default___closed__1;
                leanh::lean_inc(v_a_3510_);
                leanh::lean_inc_ref(v_a_3509_);
                v___x_3513_ = leanh::lean_apply_4(
                    v_x_3508_,
                    v___x_3512_,
                    v_a_3509_,
                    v_a_3510_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3513_) == 0 {
                    v_a_3514_ = leanh::lean_ctor_get(v___x_3513_, 0);
                    v_isSharedCheck_3524_ = (!leanh::lean_is_exclusive(v___x_3513_)) as u8;
                    if v_isSharedCheck_3524_ == 0 {
                        v___x_3516_ = v___x_3513_;
                        v_isShared_3517_ = v_isSharedCheck_3524_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3514_);
                        leanh::lean_dec(v___x_3513_);
                        v___x_3516_ = leanh::lean_box(0);
                        v_isShared_3517_ = v_isSharedCheck_3524_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3525_ = leanh::lean_ctor_get(v___x_3513_, 0);
                    v_isSharedCheck_3532_ = (!leanh::lean_is_exclusive(v___x_3513_)) as u8;
                    if v_isSharedCheck_3532_ == 0 {
                        v___x_3527_ = v___x_3513_;
                        v_isShared_3528_ = v_isSharedCheck_3532_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3525_);
                        leanh::lean_dec(v___x_3513_);
                        v___x_3527_ = leanh::lean_box(0);
                        v_isShared_3528_ = v_isSharedCheck_3532_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3518_ = leanh::lean_ctor_get(v_a_3514_, 1);
                leanh::lean_inc(v_snd_3518_);
                leanh::lean_dec(v_a_3514_);
                v_items_3519_ = leanh::lean_ctor_get(v_snd_3518_, 5);
                leanh::lean_inc_ref(v_items_3519_);
                leanh::lean_dec(v_snd_3518_);
                v___x_3520_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_3519_);
                leanh::lean_dec_ref(v_items_3519_);
                if v_isShared_3517_ == 0 {
                    leanh::lean_ctor_set(v___x_3516_, 0, v___x_3520_);
                    v___x_3522_ = v___x_3516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3523_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
                    v___x_3522_ = v_reuseFailAlloc_3523_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3522_;
            }
            3 => {
                if v_isShared_3528_ == 0 {
                    v___x_3530_ = v___x_3527_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3531_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
                    v___x_3530_ = v_reuseFailAlloc_3531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(
    mut v_x_3533_: *mut leanh::LeanObject,
    mut v_a_3534_: *mut leanh::LeanObject,
    mut v_a_3535_: *mut leanh::LeanObject,
    mut v_a_3536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3537_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(
        v_x_3533_, v_a_3534_, v_a_3535_,
    );
    leanh::lean_dec(v_a_3535_);
    leanh::lean_dec_ref(v_a_3534_);
    return v_res_3537_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(
    mut v___y_3546_: u8,
    mut v_suppressElabErrors_3547_: u8,
    mut v_x_3548_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_3548_) == 1 {
        let mut v_pre_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_3549_ = leanh::lean_ctor_get(v_x_3548_, 0);
        match leanh::lean_obj_tag(v_pre_3549_) {
            1 => {
                let mut v_pre_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_3550_ = leanh::lean_ctor_get(v_pre_3549_, 0);
                match leanh::lean_obj_tag(v_pre_3550_) {
                    0 => {
                        let mut v_str_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3554_: u8 = 0;
                        v_str_3551_ = leanh::lean_ctor_get(v_x_3548_, 1);
                        v_str_3552_ = leanh::lean_ctor_get(v_pre_3549_, 1);
                        v___x_3553_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0;
                        v___x_3554_ = lean_string_dec_eq(v_str_3552_, v___x_3553_);
                        if v___x_3554_ == 0 {
                            let mut v___x_3555_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3556_: u8 = 0;
                            v___x_3555_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1;
                            v___x_3556_ = lean_string_dec_eq(v_str_3552_, v___x_3555_);
                            if v___x_3556_ == 0 {
                                return v___y_3546_;
                            } else {
                                let mut v___x_3557_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3558_: u8 = 0;
                                v___x_3557_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2;
                                v___x_3558_ = lean_string_dec_eq(v_str_3551_, v___x_3557_);
                                if v___x_3558_ == 0 {
                                    return v___y_3546_;
                                } else {
                                    return v_suppressElabErrors_3547_;
                                }
                            }
                        } else {
                            let mut v___x_3559_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3560_: u8 = 0;
                            v___x_3559_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3;
                            v___x_3560_ = lean_string_dec_eq(v_str_3551_, v___x_3559_);
                            if v___x_3560_ == 0 {
                                return v___y_3546_;
                            } else {
                                return v_suppressElabErrors_3547_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_3561_ = leanh::lean_ctor_get(v_pre_3550_, 0);
                        if leanh::lean_obj_tag(v_pre_3561_) == 0 {
                            let mut v_str_3562_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_3563_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_3564_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3565_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3566_: u8 = 0;
                            v_str_3562_ = leanh::lean_ctor_get(v_x_3548_, 1);
                            v_str_3563_ = leanh::lean_ctor_get(v_pre_3549_, 1);
                            v_str_3564_ = leanh::lean_ctor_get(v_pre_3550_, 1);
                            v___x_3565_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4;
                            v___x_3566_ = lean_string_dec_eq(v_str_3564_, v___x_3565_);
                            if v___x_3566_ == 0 {
                                return v___y_3546_;
                            } else {
                                let mut v___x_3567_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3568_: u8 = 0;
                                v___x_3567_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5;
                                v___x_3568_ = lean_string_dec_eq(v_str_3563_, v___x_3567_);
                                if v___x_3568_ == 0 {
                                    return v___y_3546_;
                                } else {
                                    let mut v___x_3569_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3570_: u8 = 0;
                                    v___x_3569_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6;
                                    v___x_3570_ = lean_string_dec_eq(v_str_3562_, v___x_3569_);
                                    if v___x_3570_ == 0 {
                                        return v___y_3546_;
                                    } else {
                                        return v_suppressElabErrors_3547_;
                                    }
                                }
                            }
                        } else {
                            return v___y_3546_;
                        }
                    }
                    _ => {
                        return v___y_3546_;
                    }
                }
            }
            0 => {
                let mut v_str_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3573_: u8 = 0;
                v_str_3571_ = leanh::lean_ctor_get(v_x_3548_, 1);
                v___x_3572_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7;
                v___x_3573_ = lean_string_dec_eq(v_str_3571_, v___x_3572_);
                if v___x_3573_ == 0 {
                    return v___y_3546_;
                } else {
                    return v_suppressElabErrors_3547_;
                }
            }
            _ => {
                return v___y_3546_;
            }
        }
    } else {
        return v___y_3546_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(
    mut v___y_3574_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_3575_: *mut leanh::LeanObject,
    mut v_x_3576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_11747__boxed_3577_: u8 = 0;
    let mut v_suppressElabErrors_boxed_3578_: u8 = 0;
    let mut v_res_3579_: u8 = 0;
    let mut v_r_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_11747__boxed_3577_ = (leanh::lean_unbox(v___y_3574_) as u8);
    v_suppressElabErrors_boxed_3578_ = (leanh::lean_unbox(v_suppressElabErrors_3575_) as u8);
    v_res_3579_ =
        l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(
            v___y_11747__boxed_3577_,
            v_suppressElabErrors_boxed_3578_,
            v_x_3576_,
        );
    leanh::lean_dec(v_x_3576_);
    v_r_3580_ = leanh::lean_box((v_res_3579_) as usize);
    return v_r_3580_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(
    mut v_opts_3581_: *mut leanh::LeanObject,
    mut v_opt_3582_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3583_ = leanh::lean_ctor_get(v_opt_3582_, 0);
    v_defValue_3584_ = leanh::lean_ctor_get(v_opt_3582_, 1);
    v_map_3585_ = leanh::lean_ctor_get(v_opts_3581_, 0);
    v___x_3586_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3585_,
            v_name_3583_,
        );
    if leanh::lean_obj_tag(v___x_3586_) == 0 {
        let mut v___x_3587_: u8 = 0;
        v___x_3587_ = (leanh::lean_unbox(v_defValue_3584_) as u8);
        return v___x_3587_;
    } else {
        let mut v_val_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3588_ = leanh::lean_ctor_get(v___x_3586_, 0);
        leanh::lean_inc(v_val_3588_);
        leanh::lean_dec_ref_known(v___x_3586_, 1);
        if leanh::lean_obj_tag(v_val_3588_) == 1 {
            let mut v_v_3589_: u8 = 0;
            v_v_3589_ = leanh::lean_ctor_get_uint8(v_val_3588_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3588_, 0);
            return v_v_3589_;
        } else {
            let mut v___x_3590_: u8 = 0;
            leanh::lean_dec(v_val_3588_);
            v___x_3590_ = (leanh::lean_unbox(v_defValue_3584_) as u8);
            return v___x_3590_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(
    mut v_opts_3591_: *mut leanh::LeanObject,
    mut v_opt_3592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3593_: u8 = 0;
    let mut v_r_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3593_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_3591_, v_opt_3592_);
    leanh::lean_dec_ref(v_opt_3592_);
    leanh::lean_dec_ref(v_opts_3591_);
    v_r_3594_ = leanh::lean_box((v_res_3593_) as usize);
    return v_r_3594_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(
    mut v_ref_3596_: *mut leanh::LeanObject,
    mut v_msgData_3597_: *mut leanh::LeanObject,
    mut v_severity_3598_: u8,
    mut v_isSilent_3599_: u8,
    mut v___y_3600_: *mut leanh::LeanObject,
    mut v___y_3601_: *mut leanh::LeanObject,
    mut v___y_3602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3614_: u8 = 0;
    let mut v___y_3615_: u8 = 0;
    let mut v___y_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3632_: u8 = 0;
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut v___y_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3645_: u8 = 0;
    let mut v___y_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3649_: u8 = 0;
    let mut v___y_3650_: u8 = 0;
    let mut v___y_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: u8 = 0;
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3666_: u8 = 0;
    let mut v___y_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3669_: u8 = 0;
    let mut v___y_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3673_: u8 = 0;
    let mut v___y_3674_: u8 = 0;
    let mut v___y_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3680_: u8 = 0;
    let mut v___y_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3684_: u8 = 0;
    let mut v___y_3685_: u8 = 0;
    let mut v_ref_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: u8 = 0;
    let mut v___y_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3693_: u8 = 0;
    let mut v___y_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3697_: u8 = 0;
    let mut v___y_3698_: u8 = 0;
    let mut v___y_3700_: u8 = 0;
    let mut v_fileName_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3705_: u8 = 0;
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: u8 = 0;
    let mut v___x_3710_: u8 = 0;
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: u8 = 0;
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: u8 = 0;
    let mut v___x_3717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3690_ = 2;
                v___x_3716_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3598_, v___x_3690_);
                if v___x_3716_ == 0 {
                    v___y_3700_ = v___x_3716_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_3597_);
                    v___x_3717_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3597_);
                    v___y_3700_ = v___x_3717_;
                    state = 11;
                    continue;
                }
            }
            1 => {
                v___x_3606_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3606_, 0, v_a_3605_);
                leanh::lean_ctor_set(v___x_3606_, 1, v___y_3600_);
                v___x_3607_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3607_, 0, v___x_3606_);
                return v___x_3607_;
            }
            2 => {
                v___x_3618_ = lean_st_ref_take(v___y_3617_);
                v_currNamespace_3619_ = leanh::lean_ctor_get(v___y_3616_, 6);
                v_openDecls_3620_ = leanh::lean_ctor_get(v___y_3616_, 7);
                v_env_3621_ = leanh::lean_ctor_get(v___x_3618_, 0);
                v_nextMacroScope_3622_ = leanh::lean_ctor_get(v___x_3618_, 1);
                v_ngen_3623_ = leanh::lean_ctor_get(v___x_3618_, 2);
                v_auxDeclNGen_3624_ = leanh::lean_ctor_get(v___x_3618_, 3);
                v_traceState_3625_ = leanh::lean_ctor_get(v___x_3618_, 4);
                v_cache_3626_ = leanh::lean_ctor_get(v___x_3618_, 5);
                v_messages_3627_ = leanh::lean_ctor_get(v___x_3618_, 6);
                v_infoState_3628_ = leanh::lean_ctor_get(v___x_3618_, 7);
                v_snapshotTasks_3629_ = leanh::lean_ctor_get(v___x_3618_, 8);
                v_isSharedCheck_3642_ = (!leanh::lean_is_exclusive(v___x_3618_)) as u8;
                if v_isSharedCheck_3642_ == 0 {
                    v___x_3631_ = v___x_3618_;
                    v_isShared_3632_ = v_isSharedCheck_3642_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3629_);
                    leanh::lean_inc(v_infoState_3628_);
                    leanh::lean_inc(v_messages_3627_);
                    leanh::lean_inc(v_cache_3626_);
                    leanh::lean_inc(v_traceState_3625_);
                    leanh::lean_inc(v_auxDeclNGen_3624_);
                    leanh::lean_inc(v_ngen_3623_);
                    leanh::lean_inc(v_nextMacroScope_3622_);
                    leanh::lean_inc(v_env_3621_);
                    leanh::lean_dec(v___x_3618_);
                    v___x_3631_ = leanh::lean_box(0);
                    v_isShared_3632_ = v_isSharedCheck_3642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_openDecls_3620_);
                leanh::lean_inc(v_currNamespace_3619_);
                v___x_3633_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3633_, 0, v_currNamespace_3619_);
                leanh::lean_ctor_set(v___x_3633_, 1, v_openDecls_3620_);
                v___x_3634_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3634_, 0, v___x_3633_);
                leanh::lean_ctor_set(v___x_3634_, 1, v___y_3612_);
                leanh::lean_inc_ref(v___y_3613_);
                leanh::lean_inc_ref(v___y_3611_);
                v___x_3635_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_3635_, 0, v___y_3611_);
                leanh::lean_ctor_set(v___x_3635_, 1, v___y_3610_);
                leanh::lean_ctor_set(v___x_3635_, 2, v___y_3609_);
                leanh::lean_ctor_set(v___x_3635_, 3, v___y_3613_);
                leanh::lean_ctor_set(v___x_3635_, 4, v___x_3634_);
                leanh::lean_ctor_set_uint8(
                    v___x_3635_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_3615_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3635_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_3614_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3635_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3599_,
                );
                v___x_3636_ = l_Lean_MessageLog_add(v___x_3635_, v_messages_3627_);
                if v_isShared_3632_ == 0 {
                    leanh::lean_ctor_set(v___x_3631_, 6, v___x_3636_);
                    v___x_3638_ = v___x_3631_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_env_3621_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_nextMacroScope_3622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_ngen_3623_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_auxDeclNGen_3624_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 4, v_traceState_3625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 5, v_cache_3626_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 6, v___x_3636_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 7, v_infoState_3628_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 8, v_snapshotTasks_3629_);
                    v___x_3638_ = v_reuseFailAlloc_3641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3639_ = lean_st_ref_set(v___y_3617_, v___x_3638_);
                v___x_3640_ = leanh::lean_box(0);
                v_a_3605_ = v___x_3640_;
                state = 1;
                continue;
            }
            5 => {
                v___x_3652_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3597_,
                    );
                v___x_3653_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_3652_, v___y_3601_, v___y_3602_);
                v_a_3654_ = leanh::lean_ctor_get(v___x_3653_, 0);
                v_isSharedCheck_3666_ = (!leanh::lean_is_exclusive(v___x_3653_)) as u8;
                if v_isSharedCheck_3666_ == 0 {
                    v___x_3656_ = v___x_3653_;
                    v_isShared_3657_ = v_isSharedCheck_3666_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3654_);
                    leanh::lean_dec(v___x_3653_);
                    v___x_3656_ = leanh::lean_box(0);
                    v_isShared_3657_ = v_isSharedCheck_3666_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref_n(v___y_3647_, 2);
                v___x_3658_ = l_Lean_FileMap_toPosition(v___y_3647_, v___y_3646_);
                leanh::lean_dec(v___y_3646_);
                v___x_3659_ = l_Lean_FileMap_toPosition(v___y_3647_, v___y_3651_);
                leanh::lean_dec(v___y_3651_);
                if v_isShared_3657_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3656_, 1);
                    leanh::lean_ctor_set(v___x_3656_, 0, v___x_3659_);
                    v___x_3661_ = v___x_3656_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3665_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3659_);
                    v___x_3661_ = v_reuseFailAlloc_3665_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3662_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0;
                if v___y_3645_ == 0 {
                    leanh::lean_dec_ref(v___y_3644_);
                    v___y_3609_ = v___x_3661_;
                    v___y_3610_ = v___x_3658_;
                    v___y_3611_ = v___y_3648_;
                    v___y_3612_ = v_a_3654_;
                    v___y_3613_ = v___x_3662_;
                    v___y_3614_ = v___y_3650_;
                    v___y_3615_ = v___y_3649_;
                    v___y_3616_ = v___y_3601_;
                    v___y_3617_ = v___y_3602_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3654_);
                    v___x_3663_ = l_Lean_MessageData_hasTag(v___y_3644_, v_a_3654_);
                    if v___x_3663_ == 0 {
                        leanh::lean_dec_ref(v___x_3661_);
                        leanh::lean_dec_ref(v___x_3658_);
                        leanh::lean_dec(v_a_3654_);
                        v___x_3664_ = leanh::lean_box(0);
                        v_a_3605_ = v___x_3664_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3609_ = v___x_3661_;
                        v___y_3610_ = v___x_3658_;
                        v___y_3611_ = v___y_3648_;
                        v___y_3612_ = v_a_3654_;
                        v___y_3613_ = v___x_3662_;
                        v___y_3614_ = v___y_3650_;
                        v___y_3615_ = v___y_3649_;
                        v___y_3616_ = v___y_3601_;
                        v___y_3617_ = v___y_3602_;
                        state = 2;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3676_ = l_Lean_Syntax_getTailPos_x3f(v___y_3672_, v___y_3674_);
                leanh::lean_dec(v___y_3672_);
                if leanh::lean_obj_tag(v___x_3676_) == 0 {
                    leanh::lean_inc(v___y_3675_);
                    v___y_3644_ = v___y_3668_;
                    v___y_3645_ = v___y_3669_;
                    v___y_3646_ = v___y_3675_;
                    v___y_3647_ = v___y_3670_;
                    v___y_3648_ = v___y_3671_;
                    v___y_3649_ = v___y_3674_;
                    v___y_3650_ = v___y_3673_;
                    v___y_3651_ = v___y_3675_;
                    state = 5;
                    continue;
                } else {
                    v_val_3677_ = leanh::lean_ctor_get(v___x_3676_, 0);
                    leanh::lean_inc(v_val_3677_);
                    leanh::lean_dec_ref_known(v___x_3676_, 1);
                    v___y_3644_ = v___y_3668_;
                    v___y_3645_ = v___y_3669_;
                    v___y_3646_ = v___y_3675_;
                    v___y_3647_ = v___y_3670_;
                    v___y_3648_ = v___y_3671_;
                    v___y_3649_ = v___y_3674_;
                    v___y_3650_ = v___y_3673_;
                    v___y_3651_ = v_val_3677_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                v_ref_3686_ = l_Lean_replaceRef(v_ref_3596_, v___y_3682_);
                v___x_3687_ = l_Lean_Syntax_getPos_x3f(v_ref_3686_, v___y_3684_);
                if leanh::lean_obj_tag(v___x_3687_) == 0 {
                    v___x_3688_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3668_ = v___y_3679_;
                    v___y_3669_ = v___y_3680_;
                    v___y_3670_ = v___y_3681_;
                    v___y_3671_ = v___y_3683_;
                    v___y_3672_ = v_ref_3686_;
                    v___y_3673_ = v___y_3685_;
                    v___y_3674_ = v___y_3684_;
                    v___y_3675_ = v___x_3688_;
                    state = 8;
                    continue;
                } else {
                    v_val_3689_ = leanh::lean_ctor_get(v___x_3687_, 0);
                    leanh::lean_inc(v_val_3689_);
                    leanh::lean_dec_ref_known(v___x_3687_, 1);
                    v___y_3668_ = v___y_3679_;
                    v___y_3669_ = v___y_3680_;
                    v___y_3670_ = v___y_3681_;
                    v___y_3671_ = v___y_3683_;
                    v___y_3672_ = v_ref_3686_;
                    v___y_3673_ = v___y_3685_;
                    v___y_3674_ = v___y_3684_;
                    v___y_3675_ = v_val_3689_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_3698_ == 0 {
                    v___y_3679_ = v___y_3692_;
                    v___y_3680_ = v___y_3693_;
                    v___y_3681_ = v___y_3694_;
                    v___y_3682_ = v___y_3695_;
                    v___y_3683_ = v___y_3696_;
                    v___y_3684_ = v___y_3697_;
                    v___y_3685_ = v_severity_3598_;
                    state = 9;
                    continue;
                } else {
                    v___y_3679_ = v___y_3692_;
                    v___y_3680_ = v___y_3693_;
                    v___y_3681_ = v___y_3694_;
                    v___y_3682_ = v___y_3695_;
                    v___y_3683_ = v___y_3696_;
                    v___y_3684_ = v___y_3697_;
                    v___y_3685_ = v___x_3690_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                if v___y_3700_ == 0 {
                    v_fileName_3701_ = leanh::lean_ctor_get(v___y_3601_, 0);
                    v_fileMap_3702_ = leanh::lean_ctor_get(v___y_3601_, 1);
                    v_options_3703_ = leanh::lean_ctor_get(v___y_3601_, 2);
                    v_ref_3704_ = leanh::lean_ctor_get(v___y_3601_, 5);
                    v_suppressElabErrors_3705_ = leanh::lean_ctor_get_uint8(
                        v___y_3601_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3706_ = leanh::lean_box((v___y_3700_) as usize);
                    v___x_3707_ = leanh::lean_box((v_suppressElabErrors_3705_) as usize);
                    v___f_3708_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_3708_, 0, v___x_3706_);
                    leanh::lean_closure_set(v___f_3708_, 1, v___x_3707_);
                    v___x_3709_ = 1;
                    v___x_3710_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3598_, v___x_3709_);
                    if v___x_3710_ == 0 {
                        v___y_3692_ = v___f_3708_;
                        v___y_3693_ = v_suppressElabErrors_3705_;
                        v___y_3694_ = v_fileMap_3702_;
                        v___y_3695_ = v_ref_3704_;
                        v___y_3696_ = v_fileName_3701_;
                        v___y_3697_ = v___y_3700_;
                        v___y_3698_ = v___x_3710_;
                        state = 10;
                        continue;
                    } else {
                        v___x_3711_ = l_Lean_warningAsError;
                        v___x_3712_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_options_3703_, v___x_3711_);
                        v___y_3692_ = v___f_3708_;
                        v___y_3693_ = v_suppressElabErrors_3705_;
                        v___y_3694_ = v_fileMap_3702_;
                        v___y_3695_ = v_ref_3704_;
                        v___y_3696_ = v_fileName_3701_;
                        v___y_3697_ = v___y_3700_;
                        v___y_3698_ = v___x_3712_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_3597_);
                    v___x_3713_ = leanh::lean_box(0);
                    v___x_3714_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3714_, 0, v___x_3713_);
                    leanh::lean_ctor_set(v___x_3714_, 1, v___y_3600_);
                    v___x_3715_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3715_, 0, v___x_3714_);
                    return v___x_3715_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(
    mut v_ref_3718_: *mut leanh::LeanObject,
    mut v_msgData_3719_: *mut leanh::LeanObject,
    mut v_severity_3720_: *mut leanh::LeanObject,
    mut v_isSilent_3721_: *mut leanh::LeanObject,
    mut v___y_3722_: *mut leanh::LeanObject,
    mut v___y_3723_: *mut leanh::LeanObject,
    mut v___y_3724_: *mut leanh::LeanObject,
    mut v___y_3725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_3726_: u8 = 0;
    let mut v_isSilent_boxed_3727_: u8 = 0;
    let mut v_res_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3726_ = (leanh::lean_unbox(v_severity_3720_) as u8);
    v_isSilent_boxed_3727_ = (leanh::lean_unbox(v_isSilent_3721_) as u8);
    v_res_3728_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(
        v_ref_3718_,
        v_msgData_3719_,
        v_severity_boxed_3726_,
        v_isSilent_boxed_3727_,
        v___y_3722_,
        v___y_3723_,
        v___y_3724_,
    );
    leanh::lean_dec(v___y_3724_);
    leanh::lean_dec_ref(v___y_3723_);
    leanh::lean_dec(v_ref_3718_);
    return v_res_3728_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(
    mut v_ref_3729_: *mut leanh::LeanObject,
    mut v_msgData_3730_: *mut leanh::LeanObject,
    mut v___y_3731_: *mut leanh::LeanObject,
    mut v___y_3732_: *mut leanh::LeanObject,
    mut v___y_3733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3735_: u8 = 0;
    let mut v___x_3736_: u8 = 0;
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3735_ = 2;
    v___x_3736_ = 0;
    v___x_3737_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(
        v_ref_3729_,
        v_msgData_3730_,
        v___x_3735_,
        v___x_3736_,
        v___y_3731_,
        v___y_3732_,
        v___y_3733_,
    );
    return v___x_3737_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(
    mut v_ref_3738_: *mut leanh::LeanObject,
    mut v_msgData_3739_: *mut leanh::LeanObject,
    mut v___y_3740_: *mut leanh::LeanObject,
    mut v___y_3741_: *mut leanh::LeanObject,
    mut v___y_3742_: *mut leanh::LeanObject,
    mut v___y_3743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3744_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(
        v_ref_3738_,
        v_msgData_3739_,
        v___y_3740_,
        v___y_3741_,
        v___y_3742_,
    );
    leanh::lean_dec(v___y_3742_);
    leanh::lean_dec_ref(v___y_3741_);
    leanh::lean_dec(v_ref_3738_);
    return v_res_3744_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0;
    v___x_3748_ = l_Lean_MessageData_ofFormat(v___x_3747_);
    return v___x_3748_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(
    mut v_recovering_3749_: u8,
    mut v_as_3750_: *mut leanh::LeanObject,
    mut v_sz_3751_: usize,
    mut v_i_3752_: usize,
    mut v_b_3753_: u8,
    mut v___y_3754_: *mut leanh::LeanObject,
    mut v___y_3755_: *mut leanh::LeanObject,
    mut v___y_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: usize = 0;
    let mut v___x_3762_: usize = 0;
    let mut v___x_3763_: u8 = 0;
    let mut v___y_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: u8 = 0;
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3787_: u8 = 0;
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recovering_3793_: u8 = 0;
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: u8 = 0;
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3787_ = lean_usize_dec_lt(v_i_3752_, v_sz_3751_);
                if v___x_3787_ == 0 {
                    v___x_3788_ = leanh::lean_box((v_b_3753_) as usize);
                    v___x_3789_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3789_, 0, v___x_3788_);
                    leanh::lean_ctor_set(v___x_3789_, 1, v___y_3754_);
                    v___x_3790_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3790_, 0, v___x_3789_);
                    return v___x_3790_;
                } else {
                    v_a_3791_ = lean_array_uget_borrowed(v_as_3750_, v_i_3752_);
                    v___x_3792_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1;
                    leanh::lean_inc(v_a_3791_);
                    v_recovering_3793_ = l_Lean_Syntax_isOfKind(v_a_3791_, v___x_3792_);
                    if v_recovering_3793_ == 0 {
                        v___x_3794_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3;
                        leanh::lean_inc(v_a_3791_);
                        v___x_3795_ = l_Lean_Syntax_isOfKind(v_a_3791_, v___x_3794_);
                        if v___x_3795_ == 0 {
                            v___x_3796_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1;
                            leanh::lean_inc(v_a_3791_);
                            v___x_3797_ = l_Lean_Syntax_isOfKind(v_a_3791_, v___x_3796_);
                            if v___x_3797_ == 0 {
                                v___x_3798_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
                                leanh::lean_inc_ref(v___y_3754_);
                                v___x_3799_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(
                                    v_a_3791_,
                                    v___x_3798_,
                                    v___y_3754_,
                                    v___y_3755_,
                                    v___y_3756_,
                                );
                                if leanh::lean_obj_tag(v___x_3799_) == 0 {
                                    leanh::lean_dec_ref(v___y_3754_);
                                    v_a_3800_ = leanh::lean_ctor_get(v___x_3799_, 0);
                                    leanh::lean_inc(v_a_3800_);
                                    leanh::lean_dec_ref_known(v___x_3799_, 1);
                                    v_snd_3801_ = leanh::lean_ctor_get(v_a_3800_, 1);
                                    leanh::lean_inc(v_snd_3801_);
                                    leanh::lean_dec(v_a_3800_);
                                    v___x_3802_ = leanh::lean_box((v_b_3753_) as usize);
                                    v_snd_3759_ = v___x_3802_;
                                    v_snd_3760_ = v_snd_3801_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_3803_ = leanh::lean_ctor_get(v___x_3799_, 0);
                                    leanh::lean_inc(v_a_3803_);
                                    leanh::lean_dec_ref_known(v___x_3799_, 1);
                                    v_a_3784_ = v_a_3803_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_inc_ref(v___y_3754_);
                                leanh::lean_inc(v_a_3791_);
                                v___x_3804_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_3791_, v___y_3754_, v___y_3755_, v___y_3756_);
                                if leanh::lean_obj_tag(v___x_3804_) == 0 {
                                    leanh::lean_dec_ref(v___y_3754_);
                                    v_a_3805_ = leanh::lean_ctor_get(v___x_3804_, 0);
                                    leanh::lean_inc(v_a_3805_);
                                    leanh::lean_dec_ref_known(v___x_3804_, 1);
                                    v_snd_3806_ = leanh::lean_ctor_get(v_a_3805_, 1);
                                    leanh::lean_inc(v_snd_3806_);
                                    leanh::lean_dec(v_a_3805_);
                                    v___x_3807_ =
                                        leanh::lean_box((v_recovering_3793_) as usize);
                                    v_snd_3759_ = v___x_3807_;
                                    v_snd_3760_ = v_snd_3806_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_3808_ = leanh::lean_ctor_get(v___x_3804_, 0);
                                    leanh::lean_inc(v_a_3808_);
                                    leanh::lean_dec_ref_known(v___x_3804_, 1);
                                    v_a_3784_ = v_a_3808_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_inc_ref(v___y_3754_);
                            leanh::lean_inc(v_a_3791_);
                            v___x_3809_ =
                                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(
                                    v_a_3791_,
                                    v___y_3754_,
                                    v___y_3755_,
                                    v___y_3756_,
                                );
                            if leanh::lean_obj_tag(v___x_3809_) == 0 {
                                leanh::lean_dec_ref(v___y_3754_);
                                v_a_3810_ = leanh::lean_ctor_get(v___x_3809_, 0);
                                leanh::lean_inc(v_a_3810_);
                                leanh::lean_dec_ref_known(v___x_3809_, 1);
                                v_snd_3811_ = leanh::lean_ctor_get(v_a_3810_, 1);
                                leanh::lean_inc(v_snd_3811_);
                                leanh::lean_dec(v_a_3810_);
                                v___x_3812_ = leanh::lean_box((v_recovering_3793_) as usize);
                                v_snd_3759_ = v___x_3812_;
                                v_snd_3760_ = v_snd_3811_;
                                state = 1;
                                continue;
                            } else {
                                v_a_3813_ = leanh::lean_ctor_get(v___x_3809_, 0);
                                leanh::lean_inc(v_a_3813_);
                                leanh::lean_dec_ref_known(v___x_3809_, 1);
                                v_a_3784_ = v_a_3813_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        if v_b_3753_ == 0 {
                            leanh::lean_inc_ref(v___y_3754_);
                            leanh::lean_inc(v_a_3791_);
                            v___x_3814_ =
                                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(
                                    v_a_3791_,
                                    v___y_3754_,
                                    v___y_3755_,
                                    v___y_3756_,
                                );
                            if leanh::lean_obj_tag(v___x_3814_) == 0 {
                                leanh::lean_dec_ref(v___y_3754_);
                                v_a_3815_ = leanh::lean_ctor_get(v___x_3814_, 0);
                                leanh::lean_inc(v_a_3815_);
                                leanh::lean_dec_ref_known(v___x_3814_, 1);
                                v_snd_3816_ = leanh::lean_ctor_get(v_a_3815_, 1);
                                leanh::lean_inc(v_snd_3816_);
                                leanh::lean_dec(v_a_3815_);
                                v___x_3817_ = leanh::lean_box((v_b_3753_) as usize);
                                v_snd_3759_ = v___x_3817_;
                                v_snd_3760_ = v_snd_3816_;
                                state = 1;
                                continue;
                            } else {
                                v_a_3818_ = leanh::lean_ctor_get(v___x_3814_, 0);
                                leanh::lean_inc(v_a_3818_);
                                leanh::lean_dec_ref_known(v___x_3814_, 1);
                                v_a_3784_ = v_a_3818_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___x_3819_ = leanh::lean_box((v_b_3753_) as usize);
                            v_snd_3759_ = v___x_3819_;
                            v_snd_3760_ = v___y_3754_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3761_ = 1usize;
                v___x_3762_ = lean_usize_add(v_i_3752_, v___x_3761_);
                v___x_3763_ = (leanh::lean_unbox(v_snd_3759_) as u8);
                leanh::lean_dec(v_snd_3759_);
                v_i_3752_ = v___x_3762_;
                v_b_3753_ = v___x_3763_;
                v___y_3754_ = v_snd_3760_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3767_ == 0 {
                    v___x_3768_ = l_Lean_Exception_getRef(v___y_3766_);
                    v___x_3769_ = l_Lean_Exception_toMessageData(v___y_3766_);
                    v___x_3770_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(
                        v___x_3768_,
                        v___x_3769_,
                        v___y_3754_,
                        v___y_3755_,
                        v___y_3756_,
                    );
                    leanh::lean_dec(v___x_3768_);
                    if leanh::lean_obj_tag(v___x_3770_) == 0 {
                        v_a_3771_ = leanh::lean_ctor_get(v___x_3770_, 0);
                        leanh::lean_inc(v_a_3771_);
                        leanh::lean_dec_ref_known(v___x_3770_, 1);
                        v_snd_3772_ = leanh::lean_ctor_get(v_a_3771_, 1);
                        leanh::lean_inc(v_snd_3772_);
                        leanh::lean_dec(v_a_3771_);
                        v___x_3773_ = leanh::lean_box((v_recovering_3749_) as usize);
                        v_snd_3759_ = v___x_3773_;
                        v_snd_3760_ = v_snd_3772_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3774_ = leanh::lean_ctor_get(v___x_3770_, 0);
                        v_isSharedCheck_3781_ =
                            (!leanh::lean_is_exclusive(v___x_3770_)) as u8;
                        if v_isSharedCheck_3781_ == 0 {
                            v___x_3776_ = v___x_3770_;
                            v_isShared_3777_ = v_isSharedCheck_3781_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3774_);
                            leanh::lean_dec(v___x_3770_);
                            v___x_3776_ = leanh::lean_box(0);
                            v_isShared_3777_ = v_isSharedCheck_3781_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3754_);
                    v___x_3782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3782_, 0, v___y_3766_);
                    return v___x_3782_;
                }
            }
            3 => {
                if v_isShared_3777_ == 0 {
                    v___x_3779_ = v___x_3776_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
                    v___x_3779_ = v_reuseFailAlloc_3780_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3779_;
            }
            5 => {
                v___x_3785_ = l_Lean_Exception_isInterrupt(v_a_3784_);
                if v___x_3785_ == 0 {
                    leanh::lean_inc_ref(v_a_3784_);
                    v___x_3786_ = l_Lean_Exception_isRuntime(v_a_3784_);
                    v___y_3766_ = v_a_3784_;
                    v___y_3767_ = v___x_3786_;
                    state = 2;
                    continue;
                } else {
                    v___y_3766_ = v_a_3784_;
                    v___y_3767_ = v___x_3785_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(
    mut v_recovering_3820_: *mut leanh::LeanObject,
    mut v_as_3821_: *mut leanh::LeanObject,
    mut v_sz_3822_: *mut leanh::LeanObject,
    mut v_i_3823_: *mut leanh::LeanObject,
    mut v_b_3824_: *mut leanh::LeanObject,
    mut v___y_3825_: *mut leanh::LeanObject,
    mut v___y_3826_: *mut leanh::LeanObject,
    mut v___y_3827_: *mut leanh::LeanObject,
    mut v___y_3828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_recovering_boxed_3829_: u8 = 0;
    let mut v_sz_boxed_3830_: usize = 0;
    let mut v_i_boxed_3831_: usize = 0;
    let mut v_b_boxed_3832_: u8 = 0;
    let mut v_res_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_recovering_boxed_3829_ = (leanh::lean_unbox(v_recovering_3820_) as u8);
    v_sz_boxed_3830_ = leanh::lean_unbox_usize(v_sz_3822_);
    leanh::lean_dec(v_sz_3822_);
    v_i_boxed_3831_ = leanh::lean_unbox_usize(v_i_3823_);
    leanh::lean_dec(v_i_3823_);
    v_b_boxed_3832_ = (leanh::lean_unbox(v_b_3824_) as u8);
    v_res_3833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_3829_, v_as_3821_, v_sz_boxed_3830_, v_i_boxed_3831_, v_b_boxed_3832_, v___y_3825_, v___y_3826_, v___y_3827_);
    leanh::lean_dec(v___y_3827_);
    leanh::lean_dec_ref(v___y_3826_);
    leanh::lean_dec_ref(v_as_3821_);
    return v_res_3833_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(
    mut v_msg_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3838_ = leanh::lean_ctor_get(v___y_3835_, 5);
                v___x_3839_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_3834_, v___y_3835_, v___y_3836_);
                v_a_3840_ = leanh::lean_ctor_get(v___x_3839_, 0);
                v_isSharedCheck_3848_ = (!leanh::lean_is_exclusive(v___x_3839_)) as u8;
                if v_isSharedCheck_3848_ == 0 {
                    v___x_3842_ = v___x_3839_;
                    v_isShared_3843_ = v_isSharedCheck_3848_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3840_);
                    leanh::lean_dec(v___x_3839_);
                    v___x_3842_ = leanh::lean_box(0);
                    v_isShared_3843_ = v_isSharedCheck_3848_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3838_);
                v___x_3844_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3844_, 0, v_ref_3838_);
                leanh::lean_ctor_set(v___x_3844_, 1, v_a_3840_);
                if v_isShared_3843_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3842_, 1);
                    leanh::lean_ctor_set(v___x_3842_, 0, v___x_3844_);
                    v___x_3846_ = v___x_3842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3847_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
                    v___x_3846_ = v_reuseFailAlloc_3847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(
    mut v_msg_3849_: *mut leanh::LeanObject,
    mut v___y_3850_: *mut leanh::LeanObject,
    mut v___y_3851_: *mut leanh::LeanObject,
    mut v___y_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_3849_, v___y_3850_, v___y_3851_);
    leanh::lean_dec(v___y_3851_);
    leanh::lean_dec_ref(v___y_3850_);
    return v_res_3853_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(
    mut v_ref_3854_: *mut leanh::LeanObject,
    mut v_msg_3855_: *mut leanh::LeanObject,
    mut v___y_3856_: *mut leanh::LeanObject,
    mut v___y_3857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3871_: u8 = 0;
    let mut v_cancelTk_x3f_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3873_: u8 = 0;
    let mut v_inheritedTraceOptions_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3859_ = leanh::lean_ctor_get(v___y_3856_, 0);
    v_fileMap_3860_ = leanh::lean_ctor_get(v___y_3856_, 1);
    v_options_3861_ = leanh::lean_ctor_get(v___y_3856_, 2);
    v_currRecDepth_3862_ = leanh::lean_ctor_get(v___y_3856_, 3);
    v_maxRecDepth_3863_ = leanh::lean_ctor_get(v___y_3856_, 4);
    v_ref_3864_ = leanh::lean_ctor_get(v___y_3856_, 5);
    v_currNamespace_3865_ = leanh::lean_ctor_get(v___y_3856_, 6);
    v_openDecls_3866_ = leanh::lean_ctor_get(v___y_3856_, 7);
    v_initHeartbeats_3867_ = leanh::lean_ctor_get(v___y_3856_, 8);
    v_maxHeartbeats_3868_ = leanh::lean_ctor_get(v___y_3856_, 9);
    v_quotContext_3869_ = leanh::lean_ctor_get(v___y_3856_, 10);
    v_currMacroScope_3870_ = leanh::lean_ctor_get(v___y_3856_, 11);
    v_diag_3871_ = leanh::lean_ctor_get_uint8(
        v___y_3856_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3872_ = leanh::lean_ctor_get(v___y_3856_, 12);
    v_suppressElabErrors_3873_ = leanh::lean_ctor_get_uint8(
        v___y_3856_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3874_ = leanh::lean_ctor_get(v___y_3856_, 13);
    v_ref_3875_ = l_Lean_replaceRef(v_ref_3854_, v_ref_3864_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3874_);
    leanh::lean_inc(v_cancelTk_x3f_3872_);
    leanh::lean_inc(v_currMacroScope_3870_);
    leanh::lean_inc(v_quotContext_3869_);
    leanh::lean_inc(v_maxHeartbeats_3868_);
    leanh::lean_inc(v_initHeartbeats_3867_);
    leanh::lean_inc(v_openDecls_3866_);
    leanh::lean_inc(v_currNamespace_3865_);
    leanh::lean_inc(v_maxRecDepth_3863_);
    leanh::lean_inc(v_currRecDepth_3862_);
    leanh::lean_inc_ref(v_options_3861_);
    leanh::lean_inc_ref(v_fileMap_3860_);
    leanh::lean_inc_ref(v_fileName_3859_);
    v___x_3876_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3876_, 0, v_fileName_3859_);
    leanh::lean_ctor_set(v___x_3876_, 1, v_fileMap_3860_);
    leanh::lean_ctor_set(v___x_3876_, 2, v_options_3861_);
    leanh::lean_ctor_set(v___x_3876_, 3, v_currRecDepth_3862_);
    leanh::lean_ctor_set(v___x_3876_, 4, v_maxRecDepth_3863_);
    leanh::lean_ctor_set(v___x_3876_, 5, v_ref_3875_);
    leanh::lean_ctor_set(v___x_3876_, 6, v_currNamespace_3865_);
    leanh::lean_ctor_set(v___x_3876_, 7, v_openDecls_3866_);
    leanh::lean_ctor_set(v___x_3876_, 8, v_initHeartbeats_3867_);
    leanh::lean_ctor_set(v___x_3876_, 9, v_maxHeartbeats_3868_);
    leanh::lean_ctor_set(v___x_3876_, 10, v_quotContext_3869_);
    leanh::lean_ctor_set(v___x_3876_, 11, v_currMacroScope_3870_);
    leanh::lean_ctor_set(v___x_3876_, 12, v_cancelTk_x3f_3872_);
    leanh::lean_ctor_set(v___x_3876_, 13, v_inheritedTraceOptions_3874_);
    leanh::lean_ctor_set_uint8(
        v___x_3876_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3871_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3876_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3873_,
    );
    v___x_3877_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_3855_, v___x_3876_, v___y_3857_);
    leanh::lean_dec_ref_known(v___x_3876_, 14);
    return v___x_3877_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(
    mut v_ref_3878_: *mut leanh::LeanObject,
    mut v_msg_3879_: *mut leanh::LeanObject,
    mut v___y_3880_: *mut leanh::LeanObject,
    mut v___y_3881_: *mut leanh::LeanObject,
    mut v___y_3882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3883_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(
        v_ref_3878_,
        v_msg_3879_,
        v___y_3880_,
        v___y_3881_,
    );
    leanh::lean_dec(v___y_3881_);
    leanh::lean_dec_ref(v___y_3880_);
    leanh::lean_dec(v_ref_3878_);
    return v_res_3883_;
}
pub unsafe fn _init_l_Lake_Toml_elabToml___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3890_ = l_Lake_Toml_elabToml___closed__2;
    v___x_3891_ = l_Lean_stringToMessageData(v___x_3890_);
    return v___x_3891_;
}
pub unsafe fn l_Lake_Toml_elabToml(
    mut v_x_3896_: *mut leanh::LeanObject,
    mut v_a_3897_: *mut leanh::LeanObject,
    mut v_a_3898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recovering_3907_: u8 = 0;
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recovering_3913_: u8 = 0;
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3915_: usize = 0;
    let mut v___x_3916_: usize = 0;
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v_snd_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3929_: u8 = 0;
    let mut v_a_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3933_: u8 = 0;
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3900_ = l_Lake_Toml_elabToml___closed__1;
                leanh::lean_inc(v_x_3896_);
                v___x_3901_ = l_Lean_Syntax_isOfKind(v_x_3896_, v___x_3900_);
                if v___x_3901_ == 0 {
                    v___x_3902_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Toml_elabToml___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_Toml_elabToml___closed__3_once),
                        _init_l_Lake_Toml_elabToml___closed__3,
                    );
                    v___x_3903_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(
                        v_x_3896_,
                        v___x_3902_,
                        v_a_3897_,
                        v_a_3898_,
                    );
                    leanh::lean_dec(v_x_3896_);
                    return v___x_3903_;
                } else {
                    v___x_3904_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3905_ = l_Lean_Syntax_getArg(v_x_3896_, v___x_3904_);
                    v___x_3906_ = l_Lake_Toml_elabToml___closed__4;
                    v_recovering_3907_ = l_Lean_Syntax_isOfKind(v___x_3905_, v___x_3906_);
                    if v_recovering_3907_ == 0 {
                        v___x_3908_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Toml_elabToml___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_Toml_elabToml___closed__3_once),
                            _init_l_Lake_Toml_elabToml___closed__3,
                        );
                        v___x_3909_ =
                            l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(
                                v_x_3896_,
                                v___x_3908_,
                                v_a_3897_,
                                v_a_3898_,
                            );
                        leanh::lean_dec(v_x_3896_);
                        return v___x_3909_;
                    } else {
                        v___x_3910_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3911_ = l_Lean_Syntax_getArg(v_x_3896_, v___x_3910_);
                        leanh::lean_dec(v_x_3896_);
                        v_xs_3912_ = l_Lean_Syntax_getArgs(v___x_3911_);
                        leanh::lean_dec(v___x_3911_);
                        v_recovering_3913_ = 0;
                        v___x_3914_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_3912_);
                        leanh::lean_dec_ref(v_xs_3912_);
                        v_sz_3915_ = lean_array_size(v___x_3914_);
                        v___x_3916_ = 0usize;
                        v___x_3917_ = l_Lake_Toml_instInhabitedElabState_default___closed__1;
                        v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_3907_, v___x_3914_, v_sz_3915_, v___x_3916_, v_recovering_3913_, v___x_3917_, v_a_3897_, v_a_3898_);
                        leanh::lean_dec_ref(v___x_3914_);
                        if leanh::lean_obj_tag(v___x_3918_) == 0 {
                            v_a_3919_ = leanh::lean_ctor_get(v___x_3918_, 0);
                            v_isSharedCheck_3929_ =
                                (!leanh::lean_is_exclusive(v___x_3918_)) as u8;
                            if v_isSharedCheck_3929_ == 0 {
                                v___x_3921_ = v___x_3918_;
                                v_isShared_3922_ = v_isSharedCheck_3929_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3919_);
                                leanh::lean_dec(v___x_3918_);
                                v___x_3921_ = leanh::lean_box(0);
                                v_isShared_3922_ = v_isSharedCheck_3929_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3930_ = leanh::lean_ctor_get(v___x_3918_, 0);
                            v_isSharedCheck_3937_ =
                                (!leanh::lean_is_exclusive(v___x_3918_)) as u8;
                            if v_isSharedCheck_3937_ == 0 {
                                v___x_3932_ = v___x_3918_;
                                v_isShared_3933_ = v_isSharedCheck_3937_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3930_);
                                leanh::lean_dec(v___x_3918_);
                                v___x_3932_ = leanh::lean_box(0);
                                v_isShared_3933_ = v_isSharedCheck_3937_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_snd_3923_ = leanh::lean_ctor_get(v_a_3919_, 1);
                leanh::lean_inc(v_snd_3923_);
                leanh::lean_dec(v_a_3919_);
                v_items_3924_ = leanh::lean_ctor_get(v_snd_3923_, 5);
                leanh::lean_inc_ref(v_items_3924_);
                leanh::lean_dec(v_snd_3923_);
                v___x_3925_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_3924_);
                leanh::lean_dec_ref(v_items_3924_);
                if v_isShared_3922_ == 0 {
                    leanh::lean_ctor_set(v___x_3921_, 0, v___x_3925_);
                    v___x_3927_ = v___x_3921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3928_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3925_);
                    v___x_3927_ = v_reuseFailAlloc_3928_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3927_;
            }
            3 => {
                if v_isShared_3933_ == 0 {
                    v___x_3935_ = v___x_3932_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3936_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
                    v___x_3935_ = v_reuseFailAlloc_3936_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_elabToml___boxed(
    mut v_x_3938_: *mut leanh::LeanObject,
    mut v_a_3939_: *mut leanh::LeanObject,
    mut v_a_3940_: *mut leanh::LeanObject,
    mut v_a_3941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3942_ = l_Lake_Toml_elabToml(v_x_3938_, v_a_3939_, v_a_3940_);
    leanh::lean_dec(v_a_3940_);
    leanh::lean_dec_ref(v_a_3939_);
    return v_res_3942_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(
    mut v_00_u03b1_3943_: *mut leanh::LeanObject,
    mut v_ref_3944_: *mut leanh::LeanObject,
    mut v_msg_3945_: *mut leanh::LeanObject,
    mut v___y_3946_: *mut leanh::LeanObject,
    mut v___y_3947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3949_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(
        v_ref_3944_,
        v_msg_3945_,
        v___y_3946_,
        v___y_3947_,
    );
    return v___x_3949_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(
    mut v_00_u03b1_3950_: *mut leanh::LeanObject,
    mut v_ref_3951_: *mut leanh::LeanObject,
    mut v_msg_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
    mut v___y_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3956_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(
        v_00_u03b1_3950_,
        v_ref_3951_,
        v_msg_3952_,
        v___y_3953_,
        v___y_3954_,
    );
    leanh::lean_dec(v___y_3954_);
    leanh::lean_dec_ref(v___y_3953_);
    leanh::lean_dec(v_ref_3951_);
    return v_res_3956_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(
    mut v_00_u03b1_3957_: *mut leanh::LeanObject,
    mut v_msg_3958_: *mut leanh::LeanObject,
    mut v___y_3959_: *mut leanh::LeanObject,
    mut v___y_3960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3962_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_3958_, v___y_3959_, v___y_3960_);
    return v___x_3962_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(
    mut v_00_u03b1_3963_: *mut leanh::LeanObject,
    mut v_msg_3964_: *mut leanh::LeanObject,
    mut v___y_3965_: *mut leanh::LeanObject,
    mut v___y_3966_: *mut leanh::LeanObject,
    mut v___y_3967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3968_ =
        l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(
            v_00_u03b1_3963_,
            v_msg_3964_,
            v___y_3965_,
            v___y_3966_,
        );
    leanh::lean_dec(v___y_3966_);
    leanh::lean_dec_ref(v___y_3965_);
    return v_res_3968_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Elab_Expression(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Toml_Elab_Value(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_Toml_instInhabitedKeyTy_default = _init_l_Lake_Toml_instInhabitedKeyTy_default();
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy =
        _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Elab_Expression(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Toml_Grammar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Elab_Expression(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Toml_Elab_Value(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Toml_Grammar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Elab_Expression(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Elab_Expression(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Toml_Elab_Expression(builtin);
}
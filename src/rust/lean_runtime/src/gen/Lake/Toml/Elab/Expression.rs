// Lean compiler output
// Module: Lake.Toml.Elab.Expression
// Imports: Lake.Toml.Elab.Value Lake.Toml.Grammar
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_TSepArray_getElems___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr3, l_Lean_Name_str___override, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
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
    initialize_Lake_Toml_Grammar, meta_initialize_Lake_Toml_Grammar,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_4, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static mut l_Lake_Toml_instInhabitedKeyTy_default: u8 = 0;
pub static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy: u8 = 0;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3_value:
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
    m_data: [100, 111, 116, 116, 101, 100, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value:
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
    m_data: [104, 101, 97, 100, 101, 114, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value
) as *mut LeanObject;
pub static l_Lake_Toml_instInhabitedElabState_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_Toml_instInhabitedElabState_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedElabState_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_instInhabitedElabState_default___closed__1_value: LeanCtorObject<6> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_instInhabitedElabState_default___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_Toml_instInhabitedElabState_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedElabState_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_Toml_instInhabitedElabState_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedElabState_default___closed__1_value)
        as *mut LeanObject;
pub static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState:
    *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedElabState_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 97, 110, 110, 111, 116, 32, 114, 101, 100, 101, 102, 105, 110, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [32, 107, 101, 121, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 111, 109, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 108, 101, 75, 101, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut LeanObject,16525079986463702690 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value) as *mut LeanObject,15900767148364346299 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value:
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
    m_data: [107, 101, 121, 118, 97, 108, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value
) as *mut LeanObject;
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut LeanObject,16525079986463702690 as *mut LeanObject] };
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value:
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
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value
        ) as *mut LeanObject,
        1860500813421358697 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2_value:
    LeanStringObject<33> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2_value
) as *mut LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value:
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
    m_data: [107, 101, 121, 0],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value
) as *mut LeanObject;
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut LeanObject,16525079986463702690 as *mut LeanObject] };
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value:
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
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value
        ) as *mut LeanObject,
        3865642880800790572 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6_value:
    LeanStringObject<22> = LeanStringObject {
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 107, 101, 121, 32, 115, 121, 110, 116,
        97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6_value
) as *mut LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8_value
) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [40, 105, 110, 116, 101, 114, 110, 97, 108, 41, 32, 98, 97, 100, 32, 97, 114, 114, 97, 121, 32, 107, 101, 121, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_value
) as *mut LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value
) as *mut LeanObject;
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut LeanObject,16525079986463702690 as *mut LeanObject] };
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value:
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
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value
        ) as *mut LeanObject,
        14174431292734320076 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_value:
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 116, 97, 98, 108, 101, 32, 115, 121,
        110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_value
) as *mut LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value
) as *mut LeanObject;
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut LeanObject,16525079986463702690 as *mut LeanObject] };
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value) as *mut LeanObject,1392117589206424775 as *mut LeanObject] };
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2_value:
    LeanStringObject<30> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2_value
) as *mut LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value:
    LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value
) as *mut LeanObject;
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_elabToml___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_elabToml___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_elabToml___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l_Lake_Toml_elabToml___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut LeanObject,16525079986463702690 as *mut LeanObject] };
pub static l_Lake_Toml_elabToml___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__0_value) as *mut LeanObject,
        4437657283425758961 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_elabToml___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_elabToml___closed__2_value: LeanStringObject<23> = LeanStringObject {
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 84, 79, 77, 76, 32, 115, 121, 110,
        116, 97, 120, 0,
    ],
};
static mut l_Lake_Toml_elabToml___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__2_value) as *mut LeanObject;
static mut l_Lake_Toml_elabToml___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_elabToml___closed__3: *mut LeanObject = core::ptr::null_mut();
static l_Lake_Toml_elabToml___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l_Lake_Toml_elabToml___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value) as *mut LeanObject,16525079986463702690 as *mut LeanObject] };
pub static l_Lake_Toml_elabToml___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value
        ) as *mut LeanObject,
        808944059858752425 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_elabToml___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabToml___closed__4_value) as *mut LeanObject;
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx(
    mut v_x_1985_: u8,
) -> *mut LeanObject {
    match v_x_1985_ {
        0 => {
            let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
            v___x_1986_ = lean_unsigned_to_nat(0);
            return v___x_1986_;
        }
        1 => {
            let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
            v___x_1987_ = lean_unsigned_to_nat(1);
            return v___x_1987_;
        }
        2 => {
            let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
            v___x_1988_ = lean_unsigned_to_nat(2);
            return v___x_1988_;
        }
        3 => {
            let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
            v___x_1989_ = lean_unsigned_to_nat(3);
            return v___x_1989_;
        }
        _ => {
            let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
            v___x_1990_ = lean_unsigned_to_nat(4);
            return v___x_1990_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___boxed(
    mut v_x_1991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1992_: u8 = 0;
    let mut v_res_1993_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1992_ = (lean_unbox(v_x_1991_) as u8);
    v_res_1993_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx(v_x_boxed_1992_);
    return v_res_1993_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx(
    mut v_x_1994_: u8,
) -> *mut LeanObject {
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    v___x_1995_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx(v_x_1994_);
    return v___x_1995_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx___boxed(
    mut v_x_1996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1997_: u8 = 0;
    let mut v_res_1998_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1997_ = (lean_unbox(v_x_1996_) as u8);
    v_res_1998_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toCtorIdx(v_x_4__boxed_1997_);
    return v_res_1998_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(
    mut v_k_1999_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1999_);
    return v_k_1999_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg___boxed(
    mut v_k_2000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2001_: *mut LeanObject = core::ptr::null_mut();
    v_res_2001_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(v_k_2000_);
    lean_dec(v_k_2000_);
    return v_res_2001_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(
    mut v_motive_2002_: *mut LeanObject,
    mut v_ctorIdx_2003_: *mut LeanObject,
    mut v_t_2004_: u8,
    mut v_h_2005_: *mut LeanObject,
    mut v_k_2006_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2006_);
    return v_k_2006_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___boxed(
    mut v_motive_2007_: *mut LeanObject,
    mut v_ctorIdx_2008_: *mut LeanObject,
    mut v_t_2009_: *mut LeanObject,
    mut v_h_2010_: *mut LeanObject,
    mut v_k_2011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2012_: u8 = 0;
    let mut v_res_2013_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2012_ = (lean_unbox(v_t_2009_) as u8);
    v_res_2013_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(
        v_motive_2007_,
        v_ctorIdx_2008_,
        v_t_boxed_2012_,
        v_h_2010_,
        v_k_2011_,
    );
    lean_dec(v_k_2011_);
    lean_dec(v_ctorIdx_2008_);
    return v_res_2013_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(
    mut v_value_2014_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_value_2014_);
    return v_value_2014_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg___boxed(
    mut v_value_2015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2016_: *mut LeanObject = core::ptr::null_mut();
    v_res_2016_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(v_value_2015_);
    lean_dec(v_value_2015_);
    return v_res_2016_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(
    mut v_motive_2017_: *mut LeanObject,
    mut v_t_2018_: u8,
    mut v_h_2019_: *mut LeanObject,
    mut v_value_2020_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_value_2020_);
    return v_value_2020_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___boxed(
    mut v_motive_2021_: *mut LeanObject,
    mut v_t_2022_: *mut LeanObject,
    mut v_h_2023_: *mut LeanObject,
    mut v_value_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2025_: u8 = 0;
    let mut v_res_2026_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2025_ = (lean_unbox(v_t_2022_) as u8);
    v_res_2026_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(
        v_motive_2021_,
        v_t_boxed_2025_,
        v_h_2023_,
        v_value_2024_,
    );
    lean_dec(v_value_2024_);
    return v_res_2026_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(
    mut v_stdTable_2027_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_stdTable_2027_);
    return v_stdTable_2027_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg___boxed(
    mut v_stdTable_2028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2029_: *mut LeanObject = core::ptr::null_mut();
    v_res_2029_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(
        v_stdTable_2028_,
    );
    lean_dec(v_stdTable_2028_);
    return v_res_2029_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(
    mut v_motive_2030_: *mut LeanObject,
    mut v_t_2031_: u8,
    mut v_h_2032_: *mut LeanObject,
    mut v_stdTable_2033_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_stdTable_2033_);
    return v_stdTable_2033_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___boxed(
    mut v_motive_2034_: *mut LeanObject,
    mut v_t_2035_: *mut LeanObject,
    mut v_h_2036_: *mut LeanObject,
    mut v_stdTable_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2038_: u8 = 0;
    let mut v_res_2039_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2038_ = (lean_unbox(v_t_2035_) as u8);
    v_res_2039_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(
        v_motive_2034_,
        v_t_boxed_2038_,
        v_h_2036_,
        v_stdTable_2037_,
    );
    lean_dec(v_stdTable_2037_);
    return v_res_2039_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(
    mut v_array_2040_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_array_2040_);
    return v_array_2040_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg___boxed(
    mut v_array_2041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2042_: *mut LeanObject = core::ptr::null_mut();
    v_res_2042_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(v_array_2041_);
    lean_dec(v_array_2041_);
    return v_res_2042_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(
    mut v_motive_2043_: *mut LeanObject,
    mut v_t_2044_: u8,
    mut v_h_2045_: *mut LeanObject,
    mut v_array_2046_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_array_2046_);
    return v_array_2046_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___boxed(
    mut v_motive_2047_: *mut LeanObject,
    mut v_t_2048_: *mut LeanObject,
    mut v_h_2049_: *mut LeanObject,
    mut v_array_2050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2051_: u8 = 0;
    let mut v_res_2052_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2051_ = (lean_unbox(v_t_2048_) as u8);
    v_res_2052_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(
        v_motive_2047_,
        v_t_boxed_2051_,
        v_h_2049_,
        v_array_2050_,
    );
    lean_dec(v_array_2050_);
    return v_res_2052_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(
    mut v_dottedPrefix_2053_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_dottedPrefix_2053_);
    return v_dottedPrefix_2053_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg___boxed(
    mut v_dottedPrefix_2054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2055_: *mut LeanObject = core::ptr::null_mut();
    v_res_2055_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(
            v_dottedPrefix_2054_,
        );
    lean_dec(v_dottedPrefix_2054_);
    return v_res_2055_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(
    mut v_motive_2056_: *mut LeanObject,
    mut v_t_2057_: u8,
    mut v_h_2058_: *mut LeanObject,
    mut v_dottedPrefix_2059_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_dottedPrefix_2059_);
    return v_dottedPrefix_2059_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___boxed(
    mut v_motive_2060_: *mut LeanObject,
    mut v_t_2061_: *mut LeanObject,
    mut v_h_2062_: *mut LeanObject,
    mut v_dottedPrefix_2063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2064_: u8 = 0;
    let mut v_res_2065_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2064_ = (lean_unbox(v_t_2061_) as u8);
    v_res_2065_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(
        v_motive_2060_,
        v_t_boxed_2064_,
        v_h_2062_,
        v_dottedPrefix_2063_,
    );
    lean_dec(v_dottedPrefix_2063_);
    return v_res_2065_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(
    mut v_headerPrefix_2066_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_headerPrefix_2066_);
    return v_headerPrefix_2066_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg___boxed(
    mut v_headerPrefix_2067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2068_: *mut LeanObject = core::ptr::null_mut();
    v_res_2068_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(
            v_headerPrefix_2067_,
        );
    lean_dec(v_headerPrefix_2067_);
    return v_res_2068_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(
    mut v_motive_2069_: *mut LeanObject,
    mut v_t_2070_: u8,
    mut v_h_2071_: *mut LeanObject,
    mut v_headerPrefix_2072_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_headerPrefix_2072_);
    return v_headerPrefix_2072_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___boxed(
    mut v_motive_2073_: *mut LeanObject,
    mut v_t_2074_: *mut LeanObject,
    mut v_h_2075_: *mut LeanObject,
    mut v_headerPrefix_2076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2077_: u8 = 0;
    let mut v_res_2078_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2077_ = (lean_unbox(v_t_2074_) as u8);
    v_res_2078_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(
        v_motive_2073_,
        v_t_boxed_2077_,
        v_h_2075_,
        v_headerPrefix_2076_,
    );
    lean_dec(v_headerPrefix_2076_);
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
) -> *mut LeanObject {
    match v_ty_2086_ {
        0 => {
            let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
            v___x_2087_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0;
            return v___x_2087_;
        }
        1 => {
            let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
            v___x_2088_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1;
            return v___x_2088_;
        }
        2 => {
            let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
            v___x_2089_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2;
            return v___x_2089_;
        }
        3 => {
            let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
            v___x_2090_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3;
            return v___x_2090_;
        }
        _ => {
            let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
            v___x_2091_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4;
            return v___x_2091_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed(
    mut v_ty_2092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_boxed_2093_: u8 = 0;
    let mut v_res_2094_: *mut LeanObject = core::ptr::null_mut();
    v_ty_boxed_2093_ = (lean_unbox(v_ty_2092_) as u8);
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
    mut v_ty_2102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_boxed_2103_: u8 = 0;
    let mut v_res_2104_: u8 = 0;
    let mut v_r_2105_: *mut LeanObject = core::ptr::null_mut();
    v_ty_boxed_2103_ = (lean_unbox(v_ty_2102_) as u8);
    v_res_2104_ =
        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(v_ty_boxed_2103_);
    v_r_2105_ = lean_box((v_res_2104_) as usize);
    return v_r_2105_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    v___x_2114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2114_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    v___x_2115_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0);
    v___x_2116_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2116_, 0, v___x_2115_);
    return v___x_2116_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
    v___x_2118_ = lean_unsigned_to_nat(0);
    v___x_2119_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2119_, 0, v___x_2118_);
    lean_ctor_set(v___x_2119_, 1, v___x_2118_);
    lean_ctor_set(v___x_2119_, 2, v___x_2118_);
    lean_ctor_set(v___x_2119_, 3, v___x_2118_);
    lean_ctor_set(v___x_2119_, 4, v___x_2117_);
    lean_ctor_set(v___x_2119_, 5, v___x_2117_);
    lean_ctor_set(v___x_2119_, 6, v___x_2117_);
    lean_ctor_set(v___x_2119_, 7, v___x_2117_);
    lean_ctor_set(v___x_2119_, 8, v___x_2117_);
    lean_ctor_set(v___x_2119_, 9, v___x_2117_);
    return v___x_2119_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    v___x_2120_ = lean_unsigned_to_nat(32);
    v___x_2121_ = lean_mk_empty_array_with_capacity(v___x_2120_);
    v___x_2122_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2122_, 0, v___x_2121_);
    return v___x_2122_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4()
-> *mut LeanObject {
    let mut v___x_2123_: usize = 0;
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    v___x_2123_ = 5usize;
    v___x_2124_ = lean_unsigned_to_nat(0);
    v___x_2125_ = lean_unsigned_to_nat(32);
    v___x_2126_ = lean_mk_empty_array_with_capacity(v___x_2125_);
    v___x_2127_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3);
    v___x_2128_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2128_, 0, v___x_2127_);
    lean_ctor_set(v___x_2128_, 1, v___x_2126_);
    lean_ctor_set(v___x_2128_, 2, v___x_2124_);
    lean_ctor_set(v___x_2128_, 3, v___x_2124_);
    lean_ctor_set_usize(v___x_2128_, 4, v___x_2123_);
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    v___x_2129_ = lean_box(1);
    v___x_2130_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4);
    v___x_2131_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
    v___x_2132_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2132_, 0, v___x_2131_);
    lean_ctor_set(v___x_2132_, 1, v___x_2130_);
    lean_ctor_set(v___x_2132_, 2, v___x_2129_);
    return v___x_2132_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(
    mut v_msgData_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    v___x_2137_ = lean_st_ref_get(v___y_2135_);
    v_env_2138_ = lean_ctor_get(v___x_2137_, 0);
    lean_inc_ref(v_env_2138_);
    lean_dec(v___x_2137_);
    v_options_2139_ = lean_ctor_get(v___y_2134_, 2);
    v___x_2140_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2);
    v___x_2141_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5);
    lean_inc_ref(v_options_2139_);
    v___x_2142_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2142_, 0, v_env_2138_);
    lean_ctor_set(v___x_2142_, 1, v___x_2140_);
    lean_ctor_set(v___x_2142_, 2, v___x_2141_);
    lean_ctor_set(v___x_2142_, 3, v_options_2139_);
    v___x_2143_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2143_, 0, v___x_2142_);
    lean_ctor_set(v___x_2143_, 1, v_msgData_2133_);
    v___x_2144_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2144_, 0, v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2149_: *mut LeanObject = core::ptr::null_mut();
    v_res_2149_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msgData_2145_, v___y_2146_, v___y_2147_);
    lean_dec(v___y_2147_);
    lean_dec_ref(v___y_2146_);
    return v_res_2149_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(
    mut v_msg_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2159_: u8 = 0;
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2154_ = lean_ctor_get(v___y_2151_, 5);
                v___x_2155_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_2150_, v___y_2151_, v___y_2152_);
                v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
                v_isSharedCheck_2164_ = (!lean_is_exclusive(v___x_2155_)) as u8;
                if v_isSharedCheck_2164_ == 0 {
                    v___x_2158_ = v___x_2155_;
                    v_isShared_2159_ = v_isSharedCheck_2164_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2156_);
                    lean_dec(v___x_2155_);
                    v___x_2158_ = lean_box(0);
                    v_isShared_2159_ = v_isSharedCheck_2164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2154_);
                v___x_2160_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2160_, 0, v_ref_2154_);
                lean_ctor_set(v___x_2160_, 1, v_a_2156_);
                if v_isShared_2159_ == 0 {
                    lean_ctor_set_tag(v___x_2158_, 1);
                    lean_ctor_set(v___x_2158_, 0, v___x_2160_);
                    v___x_2162_ = v___x_2158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
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
    mut v_msg_2165_: *mut LeanObject,
    mut v___y_2166_: *mut LeanObject,
    mut v___y_2167_: *mut LeanObject,
    mut v___y_2168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2169_: *mut LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_2165_, v___y_2166_, v___y_2167_);
    lean_dec(v___y_2167_);
    lean_dec_ref(v___y_2166_);
    return v_res_2169_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(
    mut v_ref_2170_: *mut LeanObject,
    mut v_msg_2171_: *mut LeanObject,
    mut v___y_2172_: *mut LeanObject,
    mut v___y_2173_: *mut LeanObject,
    mut v___y_2174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2188_: u8 = 0;
    let mut v_cancelTk_x3f_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2190_: u8 = 0;
    let mut v_inheritedTraceOptions_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_2176_ = lean_ctor_get(v___y_2173_, 0);
    v_fileMap_2177_ = lean_ctor_get(v___y_2173_, 1);
    v_options_2178_ = lean_ctor_get(v___y_2173_, 2);
    v_currRecDepth_2179_ = lean_ctor_get(v___y_2173_, 3);
    v_maxRecDepth_2180_ = lean_ctor_get(v___y_2173_, 4);
    v_ref_2181_ = lean_ctor_get(v___y_2173_, 5);
    v_currNamespace_2182_ = lean_ctor_get(v___y_2173_, 6);
    v_openDecls_2183_ = lean_ctor_get(v___y_2173_, 7);
    v_initHeartbeats_2184_ = lean_ctor_get(v___y_2173_, 8);
    v_maxHeartbeats_2185_ = lean_ctor_get(v___y_2173_, 9);
    v_quotContext_2186_ = lean_ctor_get(v___y_2173_, 10);
    v_currMacroScope_2187_ = lean_ctor_get(v___y_2173_, 11);
    v_diag_2188_ = lean_ctor_get_uint8(
        v___y_2173_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2189_ = lean_ctor_get(v___y_2173_, 12);
    v_suppressElabErrors_2190_ = lean_ctor_get_uint8(
        v___y_2173_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2191_ = lean_ctor_get(v___y_2173_, 13);
    v_ref_2192_ = l_Lean_replaceRef(v_ref_2170_, v_ref_2181_);
    lean_inc_ref(v_inheritedTraceOptions_2191_);
    lean_inc(v_cancelTk_x3f_2189_);
    lean_inc(v_currMacroScope_2187_);
    lean_inc(v_quotContext_2186_);
    lean_inc(v_maxHeartbeats_2185_);
    lean_inc(v_initHeartbeats_2184_);
    lean_inc(v_openDecls_2183_);
    lean_inc(v_currNamespace_2182_);
    lean_inc(v_maxRecDepth_2180_);
    lean_inc(v_currRecDepth_2179_);
    lean_inc_ref(v_options_2178_);
    lean_inc_ref(v_fileMap_2177_);
    lean_inc_ref(v_fileName_2176_);
    v___x_2193_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_2193_, 0, v_fileName_2176_);
    lean_ctor_set(v___x_2193_, 1, v_fileMap_2177_);
    lean_ctor_set(v___x_2193_, 2, v_options_2178_);
    lean_ctor_set(v___x_2193_, 3, v_currRecDepth_2179_);
    lean_ctor_set(v___x_2193_, 4, v_maxRecDepth_2180_);
    lean_ctor_set(v___x_2193_, 5, v_ref_2192_);
    lean_ctor_set(v___x_2193_, 6, v_currNamespace_2182_);
    lean_ctor_set(v___x_2193_, 7, v_openDecls_2183_);
    lean_ctor_set(v___x_2193_, 8, v_initHeartbeats_2184_);
    lean_ctor_set(v___x_2193_, 9, v_maxHeartbeats_2185_);
    lean_ctor_set(v___x_2193_, 10, v_quotContext_2186_);
    lean_ctor_set(v___x_2193_, 11, v_currMacroScope_2187_);
    lean_ctor_set(v___x_2193_, 12, v_cancelTk_x3f_2189_);
    lean_ctor_set(v___x_2193_, 13, v_inheritedTraceOptions_2191_);
    lean_ctor_set_uint8(
        v___x_2193_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_2188_,
    );
    lean_ctor_set_uint8(
        v___x_2193_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2190_,
    );
    v___x_2194_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_2171_, v___x_2193_, v___y_2174_);
    lean_dec_ref_known(v___x_2193_, 14);
    return v___x_2194_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(
    mut v_ref_2195_: *mut LeanObject,
    mut v_msg_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
    mut v___y_2198_: *mut LeanObject,
    mut v___y_2199_: *mut LeanObject,
    mut v___y_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2201_: *mut LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_2195_, v_msg_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
    lean_dec(v___y_2199_);
    lean_dec_ref(v___y_2198_);
    lean_dec_ref(v___y_2197_);
    lean_dec(v_ref_2195_);
    return v_res_2201_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0;
    v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
    return v___x_2204_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2;
    v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
    return v___x_2207_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4;
    v___x_2210_ = l_Lean_stringToMessageData(v___x_2209_);
    return v___x_2210_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(
    mut v_as_2211_: *mut LeanObject,
    mut v_i_2212_: usize,
    mut v_stop_2213_: usize,
    mut v_b_2214_: *mut LeanObject,
    mut v___y_2215_: *mut LeanObject,
    mut v___y_2216_: *mut LeanObject,
    mut v___y_2217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: usize = 0;
    let mut v___x_2223_: usize = 0;
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyTys_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currKey_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2261_: u8 = 0;
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2265_: u8 = 0;
    let mut v_reuseFailAlloc_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2267_: u8 = 0;
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2270_: u8 = 0;
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut v_unused_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2287_: u8 = 0;
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2291_: u8 = 0;
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2225_ = lean_usize_dec_eq(v_i_2212_, v_stop_2213_);
                if v___x_2225_ == 0 {
                    v___x_2226_ = lean_array_uget_borrowed(v_as_2211_, v_i_2212_);
                    lean_inc(v___x_2226_);
                    v___x_2227_ = l_Lake_Toml_elabSimpleKey(v___x_2226_, v___y_2216_, v___y_2217_);
                    if lean_obj_tag(v___x_2227_) == 0 {
                        v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
                        lean_inc(v_a_2228_);
                        lean_dec_ref_known(v___x_2227_, 1);
                        v_keyTys_2229_ = lean_ctor_get(v___y_2215_, 0);
                        v_arrKeyTys_2230_ = lean_ctor_get(v___y_2215_, 1);
                        v_arrParents_2231_ = lean_ctor_get(v___y_2215_, 2);
                        v_currArrKey_2232_ = lean_ctor_get(v___y_2215_, 3);
                        v_currKey_2233_ = lean_ctor_get(v___y_2215_, 4);
                        v_items_2234_ = lean_ctor_get(v___y_2215_, 5);
                        v___x_2235_ = l_Lean_Name_str___override(v_b_2214_, v_a_2228_);
                        v___x_2236_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_2229_, v___x_2235_);
                        if lean_obj_tag(v___x_2236_) == 1 {
                            v_val_2237_ = lean_ctor_get(v___x_2236_, 0);
                            v_isSharedCheck_2267_ = (!lean_is_exclusive(v___x_2236_)) as u8;
                            if v_isSharedCheck_2267_ == 0 {
                                v___x_2239_ = v___x_2236_;
                                v_isShared_2240_ = v_isSharedCheck_2267_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_2237_);
                                lean_dec(v___x_2236_);
                                v___x_2239_ = lean_box(0);
                                v_isShared_2240_ = v_isSharedCheck_2267_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_inc_ref(v_items_2234_);
                            lean_inc(v_currKey_2233_);
                            lean_inc(v_currArrKey_2232_);
                            lean_inc(v_arrParents_2231_);
                            lean_inc(v_arrKeyTys_2230_);
                            lean_inc(v_keyTys_2229_);
                            lean_dec(v___x_2236_);
                            v_isSharedCheck_2277_ = (!lean_is_exclusive(v___y_2215_)) as u8;
                            if v_isSharedCheck_2277_ == 0 {
                                v_unused_2278_ = lean_ctor_get(v___y_2215_, 5);
                                lean_dec(v_unused_2278_);
                                v_unused_2279_ = lean_ctor_get(v___y_2215_, 4);
                                lean_dec(v_unused_2279_);
                                v_unused_2280_ = lean_ctor_get(v___y_2215_, 3);
                                lean_dec(v_unused_2280_);
                                v_unused_2281_ = lean_ctor_get(v___y_2215_, 2);
                                lean_dec(v_unused_2281_);
                                v_unused_2282_ = lean_ctor_get(v___y_2215_, 1);
                                lean_dec(v_unused_2282_);
                                v_unused_2283_ = lean_ctor_get(v___y_2215_, 0);
                                lean_dec(v_unused_2283_);
                                v___x_2269_ = v___y_2215_;
                                v_isShared_2270_ = v_isSharedCheck_2277_;
                                state = 6;
                                continue;
                            } else {
                                lean_dec(v___y_2215_);
                                v___x_2269_ = lean_box(0);
                                v_isShared_2270_ = v_isSharedCheck_2277_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_2215_);
                        lean_dec(v_b_2214_);
                        v_a_2284_ = lean_ctor_get(v___x_2227_, 0);
                        v_isSharedCheck_2291_ = (!lean_is_exclusive(v___x_2227_)) as u8;
                        if v_isSharedCheck_2291_ == 0 {
                            v___x_2286_ = v___x_2227_;
                            v_isShared_2287_ = v_isSharedCheck_2291_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2284_);
                            lean_dec(v___x_2227_);
                            v___x_2286_ = lean_box(0);
                            v_isShared_2287_ = v_isSharedCheck_2291_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_2292_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2292_, 0, v_b_2214_);
                    lean_ctor_set(v___x_2292_, 1, v___y_2215_);
                    v___x_2293_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2293_, 0, v___x_2292_);
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
                v___x_2241_ = (lean_unbox(v_val_2237_) as u8);
                if v___x_2241_ == 3 {
                    lean_del_object(v___x_2239_);
                    lean_dec(v_val_2237_);
                    v_fst_2220_ = v___x_2235_;
                    v_snd_2221_ = v___y_2215_;
                    state = 1;
                    continue;
                } else {
                    v___x_2242_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
                    v___x_2243_ = (lean_unbox(v_val_2237_) as u8);
                    lean_dec(v_val_2237_);
                    v___x_2244_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(
                        v___x_2243_,
                    );
                    if v_isShared_2240_ == 0 {
                        lean_ctor_set_tag(v___x_2239_, 3);
                        lean_ctor_set(v___x_2239_, 0, v___x_2244_);
                        v___x_2246_ = v___x_2239_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2266_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2244_);
                        v___x_2246_ = v_reuseFailAlloc_2266_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2247_ = l_Lean_MessageData_ofFormat(v___x_2246_);
                v___x_2248_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2248_, 0, v___x_2242_);
                lean_ctor_set(v___x_2248_, 1, v___x_2247_);
                v___x_2249_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
                v___x_2250_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2250_, 0, v___x_2248_);
                lean_ctor_set(v___x_2250_, 1, v___x_2249_);
                lean_inc(v___x_2235_);
                v___x_2251_ = l_Lean_MessageData_ofName(v___x_2235_);
                v___x_2252_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2252_, 0, v___x_2250_);
                lean_ctor_set(v___x_2252_, 1, v___x_2251_);
                v___x_2253_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                v___x_2254_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2254_, 0, v___x_2252_);
                lean_ctor_set(v___x_2254_, 1, v___x_2253_);
                v___x_2255_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2226_, v___x_2254_, v___y_2215_, v___y_2216_, v___y_2217_);
                lean_dec_ref(v___y_2215_);
                if lean_obj_tag(v___x_2255_) == 0 {
                    v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
                    lean_inc(v_a_2256_);
                    lean_dec_ref_known(v___x_2255_, 1);
                    v_snd_2257_ = lean_ctor_get(v_a_2256_, 1);
                    lean_inc(v_snd_2257_);
                    lean_dec(v_a_2256_);
                    v_fst_2220_ = v___x_2235_;
                    v_snd_2221_ = v_snd_2257_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_2235_);
                    v_a_2258_ = lean_ctor_get(v___x_2255_, 0);
                    v_isSharedCheck_2265_ = (!lean_is_exclusive(v___x_2255_)) as u8;
                    if v_isSharedCheck_2265_ == 0 {
                        v___x_2260_ = v___x_2255_;
                        v_isShared_2261_ = v_isSharedCheck_2265_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2258_);
                        lean_dec(v___x_2255_);
                        v___x_2260_ = lean_box(0);
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
                    v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
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
                v___x_2272_ = lean_box((v___x_2271_) as usize);
                lean_inc(v___x_2235_);
                v___x_2273_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2235_, v___x_2272_, v_keyTys_2229_);
                if v_isShared_2270_ == 0 {
                    lean_ctor_set(v___x_2269_, 0, v___x_2273_);
                    v___x_2275_ = v___x_2269_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
                    lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_arrKeyTys_2230_);
                    lean_ctor_set(v_reuseFailAlloc_2276_, 2, v_arrParents_2231_);
                    lean_ctor_set(v_reuseFailAlloc_2276_, 3, v_currArrKey_2232_);
                    lean_ctor_set(v_reuseFailAlloc_2276_, 4, v_currKey_2233_);
                    lean_ctor_set(v_reuseFailAlloc_2276_, 5, v_items_2234_);
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
                    v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
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
    mut v_as_2294_: *mut LeanObject,
    mut v_i_2295_: *mut LeanObject,
    mut v_stop_2296_: *mut LeanObject,
    mut v_b_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2302_: usize = 0;
    let mut v_stop_boxed_2303_: usize = 0;
    let mut v_res_2304_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2302_ = lean_unbox_usize(v_i_2295_);
    lean_dec(v_i_2295_);
    v_stop_boxed_2303_ = lean_unbox_usize(v_stop_2296_);
    lean_dec(v_stop_2296_);
    v_res_2304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_2294_, v_i_boxed_2302_, v_stop_boxed_2303_, v_b_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
    lean_dec(v___y_2300_);
    lean_dec_ref(v___y_2299_);
    lean_dec_ref(v_as_2294_);
    return v_res_2304_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(
    mut v_ks_2305_: *mut LeanObject,
    mut v_a_2306_: *mut LeanObject,
    mut v_a_2307_: *mut LeanObject,
    mut v_a_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currKey_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u8 = 0;
    v_currKey_2310_ = lean_ctor_get(v_a_2306_, 4);
    lean_inc(v_currKey_2310_);
    v___x_2311_ = lean_unsigned_to_nat(0);
    v___x_2312_ = lean_array_get_size(v_ks_2305_);
    v___x_2313_ = lean_nat_dec_lt(v___x_2311_, v___x_2312_);
    if v___x_2313_ == 0 {
        let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
        v___x_2314_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2314_, 0, v_currKey_2310_);
        lean_ctor_set(v___x_2314_, 1, v_a_2306_);
        v___x_2315_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2315_, 0, v___x_2314_);
        return v___x_2315_;
    } else {
        let mut v___x_2316_: u8 = 0;
        v___x_2316_ = lean_nat_dec_le(v___x_2312_, v___x_2312_);
        if v___x_2316_ == 0 {
            if v___x_2313_ == 0 {
                let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
                v___x_2317_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2317_, 0, v_currKey_2310_);
                lean_ctor_set(v___x_2317_, 1, v_a_2306_);
                v___x_2318_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2318_, 0, v___x_2317_);
                return v___x_2318_;
            } else {
                let mut v___x_2319_: usize = 0;
                let mut v___x_2320_: usize = 0;
                let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
                v___x_2319_ = 0usize;
                v___x_2320_ = lean_usize_of_nat(v___x_2312_);
                v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_2305_, v___x_2319_, v___x_2320_, v_currKey_2310_, v_a_2306_, v_a_2307_, v_a_2308_);
                return v___x_2321_;
            }
        } else {
            let mut v___x_2322_: usize = 0;
            let mut v___x_2323_: usize = 0;
            let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
            v___x_2322_ = 0usize;
            v___x_2323_ = lean_usize_of_nat(v___x_2312_);
            v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_2305_, v___x_2322_, v___x_2323_, v_currKey_2310_, v_a_2306_, v_a_2307_, v_a_2308_);
            return v___x_2324_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(
    mut v_ks_2325_: *mut LeanObject,
    mut v_a_2326_: *mut LeanObject,
    mut v_a_2327_: *mut LeanObject,
    mut v_a_2328_: *mut LeanObject,
    mut v_a_2329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2330_: *mut LeanObject = core::ptr::null_mut();
    v_res_2330_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(
        v_ks_2325_, v_a_2326_, v_a_2327_, v_a_2328_,
    );
    lean_dec(v_a_2328_);
    lean_dec_ref(v_a_2327_);
    lean_dec_ref(v_ks_2325_);
    return v_res_2330_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(
    mut v_00_u03b1_2331_: *mut LeanObject,
    mut v_ref_2332_: *mut LeanObject,
    mut v_msg_2333_: *mut LeanObject,
    mut v___y_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_2332_, v_msg_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
    return v___x_2338_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(
    mut v_00_u03b1_2339_: *mut LeanObject,
    mut v_ref_2340_: *mut LeanObject,
    mut v_msg_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2346_: *mut LeanObject = core::ptr::null_mut();
    v_res_2346_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_2339_, v_ref_2340_, v_msg_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
    lean_dec(v___y_2344_);
    lean_dec_ref(v___y_2343_);
    lean_dec_ref(v___y_2342_);
    lean_dec(v_ref_2340_);
    return v_res_2346_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(
    mut v_00_u03b1_2347_: *mut LeanObject,
    mut v_msg_2348_: *mut LeanObject,
    mut v___y_2349_: *mut LeanObject,
    mut v___y_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    v___x_2353_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_2348_, v___y_2350_, v___y_2351_);
    return v___x_2353_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(
    mut v_00_u03b1_2354_: *mut LeanObject,
    mut v_msg_2355_: *mut LeanObject,
    mut v___y_2356_: *mut LeanObject,
    mut v___y_2357_: *mut LeanObject,
    mut v___y_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2360_: *mut LeanObject = core::ptr::null_mut();
    v_res_2360_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_2354_, v_msg_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
    lean_dec(v___y_2358_);
    lean_dec_ref(v___y_2357_);
    lean_dec_ref(v___y_2356_);
    return v_res_2360_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(
    mut v___x_2361_: u8,
    mut v_as_2362_: *mut LeanObject,
    mut v_i_2363_: usize,
    mut v_stop_2364_: usize,
    mut v_b_2365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: usize = 0;
    let mut v___x_2369_: usize = 0;
    let mut v___x_2371_: u8 = 0;
    let mut v_fst_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u8 = 0;
    let mut v_snd_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2382_: u8 = 0;
    let mut v_unused_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2387_: u8 = 0;
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v_unused_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2371_ = lean_usize_dec_eq(v_i_2363_, v_stop_2364_);
                if v___x_2371_ == 0 {
                    v_fst_2372_ = lean_ctor_get(v_b_2365_, 0);
                    v___x_2373_ = (lean_unbox(v_fst_2372_) as u8);
                    if v___x_2373_ == 0 {
                        v_snd_2374_ = lean_ctor_get(v_b_2365_, 1);
                        v_isSharedCheck_2382_ = (!lean_is_exclusive(v_b_2365_)) as u8;
                        if v_isSharedCheck_2382_ == 0 {
                            v_unused_2383_ = lean_ctor_get(v_b_2365_, 0);
                            lean_dec(v_unused_2383_);
                            v___x_2376_ = v_b_2365_;
                            v_isShared_2377_ = v_isSharedCheck_2382_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_2374_);
                            lean_dec(v_b_2365_);
                            v___x_2376_ = lean_box(0);
                            v_isShared_2377_ = v_isSharedCheck_2382_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_2384_ = lean_ctor_get(v_b_2365_, 1);
                        v_isSharedCheck_2394_ = (!lean_is_exclusive(v_b_2365_)) as u8;
                        if v_isSharedCheck_2394_ == 0 {
                            v_unused_2395_ = lean_ctor_get(v_b_2365_, 0);
                            lean_dec(v_unused_2395_);
                            v___x_2386_ = v_b_2365_;
                            v_isShared_2387_ = v_isSharedCheck_2394_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_snd_2384_);
                            lean_dec(v_b_2365_);
                            v___x_2386_ = lean_box(0);
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
                v___x_2378_ = lean_box((v___x_2361_) as usize);
                if v_isShared_2377_ == 0 {
                    lean_ctor_set(v___x_2376_, 0, v___x_2378_);
                    v___x_2380_ = v___x_2376_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
                    lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_snd_2374_);
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
                lean_inc(v___x_2388_);
                v___x_2389_ = lean_array_push(v_snd_2384_, v___x_2388_);
                v___x_2390_ = lean_box((v___x_2371_) as usize);
                if v_isShared_2387_ == 0 {
                    lean_ctor_set(v___x_2386_, 1, v___x_2389_);
                    lean_ctor_set(v___x_2386_, 0, v___x_2390_);
                    v___x_2392_ = v___x_2386_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
                    lean_ctor_set(v_reuseFailAlloc_2393_, 1, v___x_2389_);
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
    mut v___x_2396_: *mut LeanObject,
    mut v_as_2397_: *mut LeanObject,
    mut v_i_2398_: *mut LeanObject,
    mut v_stop_2399_: *mut LeanObject,
    mut v_b_2400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4084__boxed_2401_: u8 = 0;
    let mut v_i_boxed_2402_: usize = 0;
    let mut v_stop_boxed_2403_: usize = 0;
    let mut v_res_2404_: *mut LeanObject = core::ptr::null_mut();
    v___x_4084__boxed_2401_ = (lean_unbox(v___x_2396_) as u8);
    v_i_boxed_2402_ = lean_unbox_usize(v_i_2398_);
    lean_dec(v_i_2398_);
    v_stop_boxed_2403_ = lean_unbox_usize(v_stop_2399_);
    lean_dec(v_stop_2399_);
    v_res_2404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_4084__boxed_2401_, v_as_2397_, v_i_boxed_2402_, v_stop_boxed_2403_, v_b_2400_);
    lean_dec_ref(v_as_2397_);
    return v_res_2404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(
    mut v_sz_2412_: usize,
    mut v_i_2413_: usize,
    mut v_bs_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2415_: u8 = 0;
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: usize = 0;
    let mut v___x_2424_: usize = 0;
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2415_ = lean_usize_dec_lt(v_i_2413_, v_sz_2412_);
                if v___x_2415_ == 0 {
                    v___x_2416_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2416_, 0, v_bs_2414_);
                    return v___x_2416_;
                } else {
                    v_v_2417_ = lean_array_uget(v_bs_2414_, v_i_2413_);
                    v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3;
                    lean_inc(v_v_2417_);
                    v___x_2419_ = l_Lean_Syntax_isOfKind(v_v_2417_, v___x_2418_);
                    if v___x_2419_ == 0 {
                        lean_dec(v_v_2417_);
                        lean_dec_ref(v_bs_2414_);
                        v___x_2420_ = lean_box(0);
                        return v___x_2420_;
                    } else {
                        v___x_2421_ = lean_unsigned_to_nat(0);
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
    mut v_sz_2427_: *mut LeanObject,
    mut v_i_2428_: *mut LeanObject,
    mut v_bs_2429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2430_: usize = 0;
    let mut v_i_boxed_2431_: usize = 0;
    let mut v_res_2432_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2430_ = lean_unbox_usize(v_sz_2427_);
    lean_dec(v_sz_2427_);
    v_i_boxed_2431_ = lean_unbox_usize(v_i_2428_);
    lean_dec(v_i_2428_);
    v_res_2432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_2430_, v_i_boxed_2431_, v_bs_2429_);
    return v_res_2432_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3()
-> *mut LeanObject {
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    v___x_2439_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2;
    v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
    return v___x_2440_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7()
-> *mut LeanObject {
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    v___x_2447_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6;
    v___x_2448_ = l_Lean_stringToMessageData(v___x_2447_);
    return v___x_2448_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(
    mut v_kv_2451_: *mut LeanObject,
    mut v_a_2452_: *mut LeanObject,
    mut v_a_2453_: *mut LeanObject,
    mut v_a_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2470_: usize = 0;
    let mut v___x_2471_: usize = 0;
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tailKeyStx_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyTys_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currKey_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2502_: u8 = 0;
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2518_: u8 = 0;
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2542_: u8 = 0;
    let mut v_a_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2550_: u8 = 0;
    let mut v_isSharedCheck_2551_: u8 = 0;
    let mut v_unused_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2561_: u8 = 0;
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2565_: u8 = 0;
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut v_a_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2570_: u8 = 0;
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2574_: u8 = 0;
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: u8 = 0;
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: usize = 0;
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: usize = 0;
    let mut v___x_2588_: usize = 0;
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2456_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1;
                lean_inc(v_kv_2451_);
                v___x_2457_ = l_Lean_Syntax_isOfKind(v_kv_2451_, v___x_2456_);
                if v___x_2457_ == 0 {
                    v___x_2458_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
                    v___x_2459_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_2451_, v___x_2458_, v_a_2452_, v_a_2453_, v_a_2454_);
                    lean_dec_ref(v_a_2452_);
                    lean_dec(v_kv_2451_);
                    return v___x_2459_;
                } else {
                    v___x_2460_ = lean_unsigned_to_nat(0);
                    v___x_2461_ = l_Lean_Syntax_getArg(v_kv_2451_, v___x_2460_);
                    v___x_2462_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5;
                    lean_inc(v___x_2461_);
                    v___x_2463_ = l_Lean_Syntax_isOfKind(v___x_2461_, v___x_2462_);
                    if v___x_2463_ == 0 {
                        lean_dec(v_kv_2451_);
                        v___x_2464_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                        v___x_2465_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2461_, v___x_2464_, v_a_2452_, v_a_2453_, v_a_2454_);
                        lean_dec_ref(v_a_2452_);
                        lean_dec(v___x_2461_);
                        return v___x_2465_;
                    } else {
                        v___x_2466_ = lean_unsigned_to_nat(2);
                        v_v_2467_ = l_Lean_Syntax_getArg(v_kv_2451_, v___x_2466_);
                        lean_dec(v_kv_2451_);
                        v___x_2575_ = l_Lean_Syntax_getArg(v___x_2461_, v___x_2460_);
                        v___x_2576_ = l_Lean_Syntax_getArgs(v___x_2575_);
                        lean_dec(v___x_2575_);
                        v___x_2577_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8;
                        v___x_2578_ = lean_array_get_size(v___x_2576_);
                        v___x_2579_ = lean_nat_dec_lt(v___x_2460_, v___x_2578_);
                        if v___x_2579_ == 0 {
                            lean_dec_ref(v___x_2576_);
                            v___y_2469_ = v___x_2577_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2580_ = lean_box((v___x_2463_) as usize);
                            v___x_2581_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2581_, 0, v___x_2580_);
                            lean_ctor_set(v___x_2581_, 1, v___x_2577_);
                            v___x_2582_ = lean_nat_dec_le(v___x_2578_, v___x_2578_);
                            if v___x_2582_ == 0 {
                                if v___x_2579_ == 0 {
                                    lean_dec_ref_known(v___x_2581_, 2);
                                    lean_dec_ref(v___x_2576_);
                                    v___y_2469_ = v___x_2577_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2583_ = 0usize;
                                    v___x_2584_ = lean_usize_of_nat(v___x_2578_);
                                    v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2463_, v___x_2576_, v___x_2583_, v___x_2584_, v___x_2581_);
                                    lean_dec_ref(v___x_2576_);
                                    v_snd_2586_ = lean_ctor_get(v___x_2585_, 1);
                                    lean_inc(v_snd_2586_);
                                    lean_dec_ref(v___x_2585_);
                                    v___y_2469_ = v_snd_2586_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_2587_ = 0usize;
                                v___x_2588_ = lean_usize_of_nat(v___x_2578_);
                                v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2463_, v___x_2576_, v___x_2587_, v___x_2588_, v___x_2581_);
                                lean_dec_ref(v___x_2576_);
                                v_snd_2590_ = lean_ctor_get(v___x_2589_, 1);
                                lean_inc(v_snd_2590_);
                                lean_dec_ref(v___x_2589_);
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
                if lean_obj_tag(v___x_2472_) == 0 {
                    lean_dec(v_v_2467_);
                    v___x_2473_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                    v___x_2474_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2461_, v___x_2473_, v_a_2452_, v_a_2453_, v_a_2454_);
                    lean_dec_ref(v_a_2452_);
                    lean_dec(v___x_2461_);
                    return v___x_2474_;
                } else {
                    v_val_2475_ = lean_ctor_get(v___x_2472_, 0);
                    lean_inc(v_val_2475_);
                    lean_dec_ref_known(v___x_2472_, 1);
                    v___x_2476_ = lean_box(0);
                    v___x_2477_ = lean_array_get_size(v_val_2475_);
                    v___x_2478_ = lean_unsigned_to_nat(1);
                    v___x_2479_ = lean_nat_sub(v___x_2477_, v___x_2478_);
                    v_tailKeyStx_2480_ = lean_array_get(v___x_2476_, v_val_2475_, v___x_2479_);
                    lean_dec(v___x_2479_);
                    v___x_2481_ = lean_array_pop(v_val_2475_);
                    v___x_2482_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(
                        v___x_2481_,
                        v_a_2452_,
                        v_a_2453_,
                        v_a_2454_,
                    );
                    lean_dec_ref(v___x_2481_);
                    if lean_obj_tag(v___x_2482_) == 0 {
                        v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
                        lean_inc(v_a_2483_);
                        lean_dec_ref_known(v___x_2482_, 1);
                        v_fst_2484_ = lean_ctor_get(v_a_2483_, 0);
                        v_snd_2485_ = lean_ctor_get(v_a_2483_, 1);
                        v_isSharedCheck_2566_ = (!lean_is_exclusive(v_a_2483_)) as u8;
                        if v_isSharedCheck_2566_ == 0 {
                            v___x_2487_ = v_a_2483_;
                            v_isShared_2488_ = v_isSharedCheck_2566_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_2485_);
                            lean_inc(v_fst_2484_);
                            lean_dec(v_a_2483_);
                            v___x_2487_ = lean_box(0);
                            v_isShared_2488_ = v_isSharedCheck_2566_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_tailKeyStx_2480_);
                        lean_dec(v_v_2467_);
                        lean_dec(v___x_2461_);
                        v_a_2567_ = lean_ctor_get(v___x_2482_, 0);
                        v_isSharedCheck_2574_ = (!lean_is_exclusive(v___x_2482_)) as u8;
                        if v_isSharedCheck_2574_ == 0 {
                            v___x_2569_ = v___x_2482_;
                            v_isShared_2570_ = v_isSharedCheck_2574_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_2567_);
                            lean_dec(v___x_2482_);
                            v___x_2569_ = lean_box(0);
                            v_isShared_2570_ = v_isSharedCheck_2574_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            2 => {
                lean_inc(v_tailKeyStx_2480_);
                v___x_2489_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_2480_, v_a_2453_, v_a_2454_);
                if lean_obj_tag(v___x_2489_) == 0 {
                    v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
                    lean_inc(v_a_2490_);
                    lean_dec_ref_known(v___x_2489_, 1);
                    v_keyTys_2491_ = lean_ctor_get(v_snd_2485_, 0);
                    v_arrKeyTys_2492_ = lean_ctor_get(v_snd_2485_, 1);
                    v_arrParents_2493_ = lean_ctor_get(v_snd_2485_, 2);
                    v_currArrKey_2494_ = lean_ctor_get(v_snd_2485_, 3);
                    v_currKey_2495_ = lean_ctor_get(v_snd_2485_, 4);
                    v_items_2496_ = lean_ctor_get(v_snd_2485_, 5);
                    v___x_2497_ = l_Lean_Name_str___override(v_fst_2484_, v_a_2490_);
                    v___x_2498_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_2491_, v___x_2497_);
                    if lean_obj_tag(v___x_2498_) == 1 {
                        lean_del_object(v___x_2487_);
                        lean_dec(v_v_2467_);
                        lean_dec(v___x_2461_);
                        v_val_2499_ = lean_ctor_get(v___x_2498_, 0);
                        v_isSharedCheck_2518_ = (!lean_is_exclusive(v___x_2498_)) as u8;
                        if v_isSharedCheck_2518_ == 0 {
                            v___x_2501_ = v___x_2498_;
                            v_isShared_2502_ = v_isSharedCheck_2518_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2499_);
                            lean_dec(v___x_2498_);
                            v___x_2501_ = lean_box(0);
                            v_isShared_2502_ = v_isSharedCheck_2518_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_inc_ref(v_items_2496_);
                        lean_inc(v_currKey_2495_);
                        lean_inc(v_currArrKey_2494_);
                        lean_inc(v_arrParents_2493_);
                        lean_inc(v_arrKeyTys_2492_);
                        lean_inc(v_keyTys_2491_);
                        lean_dec(v___x_2498_);
                        lean_dec(v_tailKeyStx_2480_);
                        v_isSharedCheck_2551_ = (!lean_is_exclusive(v_snd_2485_)) as u8;
                        if v_isSharedCheck_2551_ == 0 {
                            v_unused_2552_ = lean_ctor_get(v_snd_2485_, 5);
                            lean_dec(v_unused_2552_);
                            v_unused_2553_ = lean_ctor_get(v_snd_2485_, 4);
                            lean_dec(v_unused_2553_);
                            v_unused_2554_ = lean_ctor_get(v_snd_2485_, 3);
                            lean_dec(v_unused_2554_);
                            v_unused_2555_ = lean_ctor_get(v_snd_2485_, 2);
                            lean_dec(v_unused_2555_);
                            v_unused_2556_ = lean_ctor_get(v_snd_2485_, 1);
                            lean_dec(v_unused_2556_);
                            v_unused_2557_ = lean_ctor_get(v_snd_2485_, 0);
                            lean_dec(v_unused_2557_);
                            v___x_2520_ = v_snd_2485_;
                            v_isShared_2521_ = v_isSharedCheck_2551_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v_snd_2485_);
                            v___x_2520_ = lean_box(0);
                            v_isShared_2521_ = v_isSharedCheck_2551_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2487_);
                    lean_dec(v_snd_2485_);
                    lean_dec(v_fst_2484_);
                    lean_dec(v_tailKeyStx_2480_);
                    lean_dec(v_v_2467_);
                    lean_dec(v___x_2461_);
                    v_a_2558_ = lean_ctor_get(v___x_2489_, 0);
                    v_isSharedCheck_2565_ = (!lean_is_exclusive(v___x_2489_)) as u8;
                    if v_isSharedCheck_2565_ == 0 {
                        v___x_2560_ = v___x_2489_;
                        v_isShared_2561_ = v_isSharedCheck_2565_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_2558_);
                        lean_dec(v___x_2489_);
                        v___x_2560_ = lean_box(0);
                        v_isShared_2561_ = v_isSharedCheck_2565_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2503_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
                v___x_2504_ = (lean_unbox(v_val_2499_) as u8);
                lean_dec(v_val_2499_);
                v___x_2505_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_2504_);
                if v_isShared_2502_ == 0 {
                    lean_ctor_set_tag(v___x_2501_, 3);
                    lean_ctor_set(v___x_2501_, 0, v___x_2505_);
                    v___x_2507_ = v___x_2501_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2505_);
                    v___x_2507_ = v_reuseFailAlloc_2517_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2508_ = l_Lean_MessageData_ofFormat(v___x_2507_);
                v___x_2509_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2509_, 0, v___x_2503_);
                lean_ctor_set(v___x_2509_, 1, v___x_2508_);
                v___x_2510_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
                v___x_2511_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2511_, 0, v___x_2509_);
                lean_ctor_set(v___x_2511_, 1, v___x_2510_);
                v___x_2512_ = l_Lean_MessageData_ofName(v___x_2497_);
                v___x_2513_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2513_, 0, v___x_2511_);
                lean_ctor_set(v___x_2513_, 1, v___x_2512_);
                v___x_2514_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                v___x_2515_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2515_, 0, v___x_2513_);
                lean_ctor_set(v___x_2515_, 1, v___x_2514_);
                v___x_2516_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_2480_, v___x_2515_, v_snd_2485_, v_a_2453_, v_a_2454_);
                lean_dec(v_snd_2485_);
                lean_dec(v_tailKeyStx_2480_);
                return v___x_2516_;
            }
            5 => {
                v___x_2522_ = l_Lake_Toml_elabVal(v_v_2467_, v_a_2453_, v_a_2454_);
                if lean_obj_tag(v___x_2522_) == 0 {
                    v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
                    v_isSharedCheck_2542_ = (!lean_is_exclusive(v___x_2522_)) as u8;
                    if v_isSharedCheck_2542_ == 0 {
                        v___x_2525_ = v___x_2522_;
                        v_isShared_2526_ = v_isSharedCheck_2542_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2523_);
                        lean_dec(v___x_2522_);
                        v___x_2525_ = lean_box(0);
                        v_isShared_2526_ = v_isSharedCheck_2542_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2520_);
                    lean_dec(v___x_2497_);
                    lean_dec_ref(v_items_2496_);
                    lean_dec(v_currKey_2495_);
                    lean_dec(v_currArrKey_2494_);
                    lean_dec(v_arrParents_2493_);
                    lean_dec(v_arrKeyTys_2492_);
                    lean_dec(v_keyTys_2491_);
                    lean_del_object(v___x_2487_);
                    lean_dec(v___x_2461_);
                    v_a_2543_ = lean_ctor_get(v___x_2522_, 0);
                    v_isSharedCheck_2550_ = (!lean_is_exclusive(v___x_2522_)) as u8;
                    if v_isSharedCheck_2550_ == 0 {
                        v___x_2545_ = v___x_2522_;
                        v_isShared_2546_ = v_isSharedCheck_2550_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2543_);
                        lean_dec(v___x_2522_);
                        v___x_2545_ = lean_box(0);
                        v_isShared_2546_ = v_isSharedCheck_2550_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2527_ = lean_box(0);
                v___x_2528_ = 0;
                v___x_2529_ = lean_box((v___x_2528_) as usize);
                lean_inc(v___x_2497_);
                v___x_2530_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2497_, v___x_2529_, v_keyTys_2491_);
                v___x_2531_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2531_, 0, v___x_2461_);
                lean_ctor_set(v___x_2531_, 1, v___x_2497_);
                lean_ctor_set(v___x_2531_, 2, v_a_2523_);
                v___x_2532_ = lean_array_push(v_items_2496_, v___x_2531_);
                if v_isShared_2521_ == 0 {
                    lean_ctor_set(v___x_2520_, 5, v___x_2532_);
                    lean_ctor_set(v___x_2520_, 0, v___x_2530_);
                    v___x_2534_ = v___x_2520_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2530_);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_arrKeyTys_2492_);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_arrParents_2493_);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 3, v_currArrKey_2494_);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 4, v_currKey_2495_);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 5, v___x_2532_);
                    v___x_2534_ = v_reuseFailAlloc_2541_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2488_ == 0 {
                    lean_ctor_set(v___x_2487_, 1, v___x_2534_);
                    lean_ctor_set(v___x_2487_, 0, v___x_2527_);
                    v___x_2536_ = v___x_2487_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2527_);
                    lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___x_2534_);
                    v___x_2536_ = v_reuseFailAlloc_2540_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2526_ == 0 {
                    lean_ctor_set(v___x_2525_, 0, v___x_2536_);
                    v___x_2538_ = v___x_2525_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
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
                    v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
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
                    v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
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
                    v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
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
    mut v_kv_2591_: *mut LeanObject,
    mut v_a_2592_: *mut LeanObject,
    mut v_a_2593_: *mut LeanObject,
    mut v_a_2594_: *mut LeanObject,
    mut v_a_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2596_: *mut LeanObject = core::ptr::null_mut();
    v_res_2596_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(
        v_kv_2591_, v_a_2592_, v_a_2593_, v_a_2594_,
    );
    lean_dec(v_a_2594_);
    lean_dec_ref(v_a_2593_);
    return v_res_2596_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0;
    v___x_2599_ = l_Lean_stringToMessageData(v___x_2598_);
    return v___x_2599_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(
    mut v_as_2600_: *mut LeanObject,
    mut v_i_2601_: usize,
    mut v_stop_2602_: usize,
    mut v_b_2603_: *mut LeanObject,
    mut v___y_2604_: *mut LeanObject,
    mut v___y_2605_: *mut LeanObject,
    mut v___y_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: usize = 0;
    let mut v___x_2612_: usize = 0;
    let mut v___x_2614_: u8 = 0;
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyTys_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currKey_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2630_: u8 = 0;
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2633_: u8 = 0;
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2650_: u8 = 0;
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2654_: u8 = 0;
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_unused_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: u8 = 0;
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2685_: u8 = 0;
    let mut v_reuseFailAlloc_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2687_: u8 = 0;
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2690_: u8 = 0;
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_unused_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2707_: u8 = 0;
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2711_: u8 = 0;
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2614_ = lean_usize_dec_eq(v_i_2601_, v_stop_2602_);
                if v___x_2614_ == 0 {
                    v___x_2615_ = lean_array_uget_borrowed(v_as_2600_, v_i_2601_);
                    lean_inc(v___x_2615_);
                    v___x_2616_ = l_Lake_Toml_elabSimpleKey(v___x_2615_, v___y_2605_, v___y_2606_);
                    if lean_obj_tag(v___x_2616_) == 0 {
                        v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
                        lean_inc(v_a_2617_);
                        lean_dec_ref_known(v___x_2616_, 1);
                        v_keyTys_2618_ = lean_ctor_get(v___y_2604_, 0);
                        v_arrKeyTys_2619_ = lean_ctor_get(v___y_2604_, 1);
                        v_arrParents_2620_ = lean_ctor_get(v___y_2604_, 2);
                        v_currArrKey_2621_ = lean_ctor_get(v___y_2604_, 3);
                        v_currKey_2622_ = lean_ctor_get(v___y_2604_, 4);
                        v_items_2623_ = lean_ctor_get(v___y_2604_, 5);
                        v___x_2624_ = l_Lean_Name_str___override(v_b_2603_, v_a_2617_);
                        v___x_2625_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_2618_, v___x_2624_);
                        if lean_obj_tag(v___x_2625_) == 1 {
                            v_val_2626_ = lean_ctor_get(v___x_2625_, 0);
                            v_isSharedCheck_2687_ = (!lean_is_exclusive(v___x_2625_)) as u8;
                            if v_isSharedCheck_2687_ == 0 {
                                v___x_2628_ = v___x_2625_;
                                v_isShared_2629_ = v_isSharedCheck_2687_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_2626_);
                                lean_dec(v___x_2625_);
                                v___x_2628_ = lean_box(0);
                                v_isShared_2629_ = v_isSharedCheck_2687_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_inc_ref(v_items_2623_);
                            lean_inc(v_currKey_2622_);
                            lean_inc(v_currArrKey_2621_);
                            lean_inc(v_arrParents_2620_);
                            lean_inc(v_arrKeyTys_2619_);
                            lean_inc(v_keyTys_2618_);
                            lean_dec(v___x_2625_);
                            v_isSharedCheck_2697_ = (!lean_is_exclusive(v___y_2604_)) as u8;
                            if v_isSharedCheck_2697_ == 0 {
                                v_unused_2698_ = lean_ctor_get(v___y_2604_, 5);
                                lean_dec(v_unused_2698_);
                                v_unused_2699_ = lean_ctor_get(v___y_2604_, 4);
                                lean_dec(v_unused_2699_);
                                v_unused_2700_ = lean_ctor_get(v___y_2604_, 3);
                                lean_dec(v_unused_2700_);
                                v_unused_2701_ = lean_ctor_get(v___y_2604_, 2);
                                lean_dec(v_unused_2701_);
                                v_unused_2702_ = lean_ctor_get(v___y_2604_, 1);
                                lean_dec(v_unused_2702_);
                                v_unused_2703_ = lean_ctor_get(v___y_2604_, 0);
                                lean_dec(v_unused_2703_);
                                v___x_2689_ = v___y_2604_;
                                v_isShared_2690_ = v_isSharedCheck_2697_;
                                state = 10;
                                continue;
                            } else {
                                lean_dec(v___y_2604_);
                                v___x_2689_ = lean_box(0);
                                v_isShared_2690_ = v_isSharedCheck_2697_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_2604_);
                        lean_dec(v_b_2603_);
                        v_a_2704_ = lean_ctor_get(v___x_2616_, 0);
                        v_isSharedCheck_2711_ = (!lean_is_exclusive(v___x_2616_)) as u8;
                        if v_isSharedCheck_2711_ == 0 {
                            v___x_2706_ = v___x_2616_;
                            v_isShared_2707_ = v_isSharedCheck_2711_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2704_);
                            lean_dec(v___x_2616_);
                            v___x_2706_ = lean_box(0);
                            v_isShared_2707_ = v_isSharedCheck_2711_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    v___x_2712_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2712_, 0, v_b_2603_);
                    lean_ctor_set(v___x_2712_, 1, v___y_2604_);
                    v___x_2713_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2713_, 0, v___x_2712_);
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
                v___x_2630_ = (lean_unbox(v_val_2626_) as u8);
                match v___x_2630_ {
                    2 => {
                        lean_inc_ref(v_items_2623_);
                        lean_inc(v_currKey_2622_);
                        lean_inc(v_arrParents_2620_);
                        lean_inc(v_arrKeyTys_2619_);
                        lean_del_object(v___x_2628_);
                        lean_dec(v_val_2626_);
                        v_isSharedCheck_2655_ = (!lean_is_exclusive(v___y_2604_)) as u8;
                        if v_isSharedCheck_2655_ == 0 {
                            v_unused_2656_ = lean_ctor_get(v___y_2604_, 5);
                            lean_dec(v_unused_2656_);
                            v_unused_2657_ = lean_ctor_get(v___y_2604_, 4);
                            lean_dec(v_unused_2657_);
                            v_unused_2658_ = lean_ctor_get(v___y_2604_, 3);
                            lean_dec(v_unused_2658_);
                            v_unused_2659_ = lean_ctor_get(v___y_2604_, 2);
                            lean_dec(v_unused_2659_);
                            v_unused_2660_ = lean_ctor_get(v___y_2604_, 1);
                            lean_dec(v_unused_2660_);
                            v_unused_2661_ = lean_ctor_get(v___y_2604_, 0);
                            lean_dec(v_unused_2661_);
                            v___x_2632_ = v___y_2604_;
                            v_isShared_2633_ = v_isSharedCheck_2655_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___y_2604_);
                            v___x_2632_ = lean_box(0);
                            v_isShared_2633_ = v_isSharedCheck_2655_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        lean_del_object(v___x_2628_);
                        lean_dec(v_val_2626_);
                        v_fst_2609_ = v___x_2624_;
                        v_snd_2610_ = v___y_2604_;
                        state = 1;
                        continue;
                    }
                    4 => {
                        lean_del_object(v___x_2628_);
                        lean_dec(v_val_2626_);
                        v_fst_2609_ = v___x_2624_;
                        v_snd_2610_ = v___y_2604_;
                        state = 1;
                        continue;
                    }
                    3 => {
                        lean_del_object(v___x_2628_);
                        lean_dec(v_val_2626_);
                        v_fst_2609_ = v___x_2624_;
                        v_snd_2610_ = v___y_2604_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2662_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
                        v___x_2663_ = (lean_unbox(v_val_2626_) as u8);
                        lean_dec(v_val_2626_);
                        v___x_2664_ =
                            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(
                                v___x_2663_,
                            );
                        if v_isShared_2629_ == 0 {
                            lean_ctor_set_tag(v___x_2628_, 3);
                            lean_ctor_set(v___x_2628_, 0, v___x_2664_);
                            v___x_2666_ = v___x_2628_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_2686_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2664_);
                            v___x_2666_ = v_reuseFailAlloc_2686_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2634_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_2619_, v___x_2624_);
                if lean_obj_tag(v___x_2634_) == 1 {
                    v_val_2635_ = lean_ctor_get(v___x_2634_, 0);
                    lean_inc(v_val_2635_);
                    lean_dec_ref_known(v___x_2634_, 1);
                    lean_inc(v___x_2624_);
                    if v_isShared_2633_ == 0 {
                        lean_ctor_set(v___x_2632_, 3, v___x_2624_);
                        lean_ctor_set(v___x_2632_, 0, v_val_2635_);
                        v___x_2637_ = v___x_2632_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 6, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_val_2635_);
                        lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_arrKeyTys_2619_);
                        lean_ctor_set(v_reuseFailAlloc_2638_, 2, v_arrParents_2620_);
                        lean_ctor_set(v_reuseFailAlloc_2638_, 3, v___x_2624_);
                        lean_ctor_set(v_reuseFailAlloc_2638_, 4, v_currKey_2622_);
                        lean_ctor_set(v_reuseFailAlloc_2638_, 5, v_items_2623_);
                        v___x_2637_ = v_reuseFailAlloc_2638_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2634_);
                    lean_del_object(v___x_2632_);
                    lean_dec_ref(v_items_2623_);
                    lean_dec(v_currKey_2622_);
                    lean_dec(v_arrParents_2620_);
                    lean_dec(v_arrKeyTys_2619_);
                    v___x_2639_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
                    lean_inc(v___x_2624_);
                    v___x_2640_ = l_Lean_MessageData_ofName(v___x_2624_);
                    v___x_2641_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2641_, 0, v___x_2639_);
                    lean_ctor_set(v___x_2641_, 1, v___x_2640_);
                    v___x_2642_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                    v___x_2643_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2643_, 0, v___x_2641_);
                    lean_ctor_set(v___x_2643_, 1, v___x_2642_);
                    v___x_2644_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_2643_, v___y_2605_, v___y_2606_);
                    if lean_obj_tag(v___x_2644_) == 0 {
                        v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
                        lean_inc(v_a_2645_);
                        lean_dec_ref_known(v___x_2644_, 1);
                        v_snd_2646_ = lean_ctor_get(v_a_2645_, 1);
                        lean_inc(v_snd_2646_);
                        lean_dec(v_a_2645_);
                        v_fst_2609_ = v___x_2624_;
                        v_snd_2610_ = v_snd_2646_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2624_);
                        v_a_2647_ = lean_ctor_get(v___x_2644_, 0);
                        v_isSharedCheck_2654_ = (!lean_is_exclusive(v___x_2644_)) as u8;
                        if v_isSharedCheck_2654_ == 0 {
                            v___x_2649_ = v___x_2644_;
                            v_isShared_2650_ = v_isSharedCheck_2654_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2647_);
                            lean_dec(v___x_2644_);
                            v___x_2649_ = lean_box(0);
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
                    v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
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
                v___x_2668_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2668_, 0, v___x_2662_);
                lean_ctor_set(v___x_2668_, 1, v___x_2667_);
                v___x_2669_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
                v___x_2670_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2670_, 0, v___x_2668_);
                lean_ctor_set(v___x_2670_, 1, v___x_2669_);
                lean_inc(v___x_2624_);
                v___x_2671_ = l_Lean_MessageData_ofName(v___x_2624_);
                v___x_2672_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2672_, 0, v___x_2670_);
                lean_ctor_set(v___x_2672_, 1, v___x_2671_);
                v___x_2673_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                v___x_2674_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2674_, 0, v___x_2672_);
                lean_ctor_set(v___x_2674_, 1, v___x_2673_);
                v___x_2675_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2615_, v___x_2674_, v___y_2604_, v___y_2605_, v___y_2606_);
                lean_dec_ref(v___y_2604_);
                if lean_obj_tag(v___x_2675_) == 0 {
                    v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
                    lean_inc(v_a_2676_);
                    lean_dec_ref_known(v___x_2675_, 1);
                    v_snd_2677_ = lean_ctor_get(v_a_2676_, 1);
                    lean_inc(v_snd_2677_);
                    lean_dec(v_a_2676_);
                    v_fst_2609_ = v___x_2624_;
                    v_snd_2610_ = v_snd_2677_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_2624_);
                    v_a_2678_ = lean_ctor_get(v___x_2675_, 0);
                    v_isSharedCheck_2685_ = (!lean_is_exclusive(v___x_2675_)) as u8;
                    if v_isSharedCheck_2685_ == 0 {
                        v___x_2680_ = v___x_2675_;
                        v_isShared_2681_ = v_isSharedCheck_2685_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2678_);
                        lean_dec(v___x_2675_);
                        v___x_2680_ = lean_box(0);
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
                    v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
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
                v___x_2692_ = lean_box((v___x_2691_) as usize);
                lean_inc(v___x_2624_);
                v___x_2693_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2624_, v___x_2692_, v_keyTys_2618_);
                if v_isShared_2690_ == 0 {
                    lean_ctor_set(v___x_2689_, 0, v___x_2693_);
                    v___x_2695_ = v___x_2689_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
                    lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_arrKeyTys_2619_);
                    lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_arrParents_2620_);
                    lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_currArrKey_2621_);
                    lean_ctor_set(v_reuseFailAlloc_2696_, 4, v_currKey_2622_);
                    lean_ctor_set(v_reuseFailAlloc_2696_, 5, v_items_2623_);
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
                    v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
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
    mut v_as_2714_: *mut LeanObject,
    mut v_i_2715_: *mut LeanObject,
    mut v_stop_2716_: *mut LeanObject,
    mut v_b_2717_: *mut LeanObject,
    mut v___y_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2722_: usize = 0;
    let mut v_stop_boxed_2723_: usize = 0;
    let mut v_res_2724_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2722_ = lean_unbox_usize(v_i_2715_);
    lean_dec(v_i_2715_);
    v_stop_boxed_2723_ = lean_unbox_usize(v_stop_2716_);
    lean_dec(v_stop_2716_);
    v_res_2724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_2714_, v_i_boxed_2722_, v_stop_boxed_2723_, v_b_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
    lean_dec(v___y_2720_);
    lean_dec_ref(v___y_2719_);
    lean_dec_ref(v_as_2714_);
    return v_res_2724_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(
    mut v_t_2725_: *mut LeanObject,
    mut v_k_2726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: u8 = 0;
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2725_) == 0 {
                    v_k_2727_ = lean_ctor_get(v_t_2725_, 1);
                    v_v_2728_ = lean_ctor_get(v_t_2725_, 2);
                    v_l_2729_ = lean_ctor_get(v_t_2725_, 3);
                    v_r_2730_ = lean_ctor_get(v_t_2725_, 4);
                    v___x_2731_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2726_, v_k_2727_);
                    match v___x_2731_ {
                        0 => {
                            v_t_2725_ = v_l_2729_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_2728_);
                            v___x_2733_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2733_, 0, v_v_2728_);
                            return v___x_2733_;
                        }
                        _ => {
                            v_t_2725_ = v_r_2730_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2735_ = lean_box(0);
                    return v___x_2735_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(
    mut v_t_2736_: *mut LeanObject,
    mut v_k_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2738_: *mut LeanObject = core::ptr::null_mut();
    v_res_2738_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_2736_, v_k_2737_);
    lean_dec(v_k_2737_);
    lean_dec(v_t_2736_);
    return v_res_2738_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(
    mut v_ks_2739_: *mut LeanObject,
    mut v_a_2740_: *mut LeanObject,
    mut v_a_2741_: *mut LeanObject,
    mut v_a_2742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keyTys_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currKey_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v_arrKeyTys_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: u8 = 0;
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: usize = 0;
    let mut v___x_2768_: usize = 0;
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: usize = 0;
    let mut v___x_2771_: usize = 0;
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_keyTys_2744_ = lean_ctor_get(v_a_2740_, 0);
                v_arrKeyTys_2745_ = lean_ctor_get(v_a_2740_, 1);
                v_arrParents_2746_ = lean_ctor_get(v_a_2740_, 2);
                v_currArrKey_2747_ = lean_ctor_get(v_a_2740_, 3);
                v_currKey_2748_ = lean_ctor_get(v_a_2740_, 4);
                v_items_2749_ = lean_ctor_get(v_a_2740_, 5);
                v_isSharedCheck_2777_ = (!lean_is_exclusive(v_a_2740_)) as u8;
                if v_isSharedCheck_2777_ == 0 {
                    v___x_2751_ = v_a_2740_;
                    v_isShared_2752_ = v_isSharedCheck_2777_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_items_2749_);
                    lean_inc(v_currKey_2748_);
                    lean_inc(v_currArrKey_2747_);
                    lean_inc(v_arrParents_2746_);
                    lean_inc(v_arrKeyTys_2745_);
                    lean_inc(v_keyTys_2744_);
                    lean_dec(v_a_2740_);
                    v___x_2751_ = lean_box(0);
                    v_isShared_2752_ = v_isSharedCheck_2777_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_arrKeyTys_2753_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_2747_, v_keyTys_2744_, v_arrKeyTys_2745_);
                v___x_2754_ = lean_box(0);
                v___x_2774_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_2753_, v___x_2754_);
                if lean_obj_tag(v___x_2774_) == 0 {
                    v___x_2775_ = lean_box(1);
                    v___y_2756_ = v___x_2775_;
                    state = 2;
                    continue;
                } else {
                    v_val_2776_ = lean_ctor_get(v___x_2774_, 0);
                    lean_inc(v_val_2776_);
                    lean_dec_ref_known(v___x_2774_, 1);
                    v___y_2756_ = v_val_2776_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2752_ == 0 {
                    lean_ctor_set(v___x_2751_, 3, v___x_2754_);
                    lean_ctor_set(v___x_2751_, 1, v_arrKeyTys_2753_);
                    lean_ctor_set(v___x_2751_, 0, v___y_2756_);
                    v___x_2758_ = v___x_2751_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___y_2756_);
                    lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_arrKeyTys_2753_);
                    lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_arrParents_2746_);
                    lean_ctor_set(v_reuseFailAlloc_2773_, 3, v___x_2754_);
                    lean_ctor_set(v_reuseFailAlloc_2773_, 4, v_currKey_2748_);
                    lean_ctor_set(v_reuseFailAlloc_2773_, 5, v_items_2749_);
                    v___x_2758_ = v_reuseFailAlloc_2773_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2759_ = lean_unsigned_to_nat(0);
                v___x_2760_ = lean_array_get_size(v_ks_2739_);
                v___x_2761_ = lean_nat_dec_lt(v___x_2759_, v___x_2760_);
                if v___x_2761_ == 0 {
                    v___x_2762_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2762_, 0, v___x_2754_);
                    lean_ctor_set(v___x_2762_, 1, v___x_2758_);
                    v___x_2763_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2763_, 0, v___x_2762_);
                    return v___x_2763_;
                } else {
                    v___x_2764_ = lean_nat_dec_le(v___x_2760_, v___x_2760_);
                    if v___x_2764_ == 0 {
                        if v___x_2761_ == 0 {
                            v___x_2765_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2765_, 0, v___x_2754_);
                            lean_ctor_set(v___x_2765_, 1, v___x_2758_);
                            v___x_2766_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2766_, 0, v___x_2765_);
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
    mut v_ks_2778_: *mut LeanObject,
    mut v_a_2779_: *mut LeanObject,
    mut v_a_2780_: *mut LeanObject,
    mut v_a_2781_: *mut LeanObject,
    mut v_a_2782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2783_: *mut LeanObject = core::ptr::null_mut();
    v_res_2783_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(
        v_ks_2778_, v_a_2779_, v_a_2780_, v_a_2781_,
    );
    lean_dec(v_a_2781_);
    lean_dec_ref(v_a_2780_);
    lean_dec_ref(v_ks_2778_);
    return v_res_2783_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(
    mut v_00_u03b4_2784_: *mut LeanObject,
    mut v_t_2785_: *mut LeanObject,
    mut v_k_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    v___x_2787_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_2785_, v_k_2786_);
    return v___x_2787_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(
    mut v_00_u03b4_2788_: *mut LeanObject,
    mut v_t_2789_: *mut LeanObject,
    mut v_k_2790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2791_: *mut LeanObject = core::ptr::null_mut();
    v_res_2791_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_2788_, v_t_2789_, v_k_2790_);
    lean_dec(v_k_2790_);
    lean_dec(v_t_2789_);
    return v_res_2791_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1()
-> *mut LeanObject {
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    v___x_2793_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0;
    v___x_2794_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_2793_);
    return v___x_2794_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5()
-> *mut LeanObject {
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    v___x_2801_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4;
    v___x_2802_ = l_Lean_stringToMessageData(v___x_2801_);
    return v___x_2802_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(
    mut v_x_2803_: *mut LeanObject,
    mut v_a_2804_: *mut LeanObject,
    mut v_a_2805_: *mut LeanObject,
    mut v_a_2806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyTys_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2838_: u8 = 0;
    let mut v_cancelTk_x3f_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2840_: u8 = 0;
    let mut v_inheritedTraceOptions_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: u8 = 0;
    let mut v_ref_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2852_: usize = 0;
    let mut v___x_2853_: usize = 0;
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tailKey_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyTys_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrParents_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2882_: u8 = 0;
    let mut v___x_2883_: u8 = 0;
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: u8 = 0;
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut v_a_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2909_: u8 = 0;
    let mut v_isSharedCheck_2910_: u8 = 0;
    let mut v_a_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2914_: u8 = 0;
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2918_: u8 = 0;
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: u8 = 0;
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: u8 = 0;
    let mut v___x_2932_: usize = 0;
    let mut v___x_2933_: usize = 0;
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: usize = 0;
    let mut v___x_2937_: usize = 0;
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2826_ = lean_ctor_get(v_a_2805_, 0);
                v_fileMap_2827_ = lean_ctor_get(v_a_2805_, 1);
                v_options_2828_ = lean_ctor_get(v_a_2805_, 2);
                v_currRecDepth_2829_ = lean_ctor_get(v_a_2805_, 3);
                v_maxRecDepth_2830_ = lean_ctor_get(v_a_2805_, 4);
                v_ref_2831_ = lean_ctor_get(v_a_2805_, 5);
                v_currNamespace_2832_ = lean_ctor_get(v_a_2805_, 6);
                v_openDecls_2833_ = lean_ctor_get(v_a_2805_, 7);
                v_initHeartbeats_2834_ = lean_ctor_get(v_a_2805_, 8);
                v_maxHeartbeats_2835_ = lean_ctor_get(v_a_2805_, 9);
                v_quotContext_2836_ = lean_ctor_get(v_a_2805_, 10);
                v_currMacroScope_2837_ = lean_ctor_get(v_a_2805_, 11);
                v_diag_2838_ = lean_ctor_get_uint8(
                    v_a_2805_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2839_ = lean_ctor_get(v_a_2805_, 12);
                v_suppressElabErrors_2840_ = lean_ctor_get_uint8(
                    v_a_2805_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2841_ = lean_ctor_get(v_a_2805_, 13);
                v___x_2842_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3;
                lean_inc(v_x_2803_);
                v___x_2843_ = l_Lean_Syntax_isOfKind(v_x_2803_, v___x_2842_);
                v_ref_2844_ = l_Lean_replaceRef(v_x_2803_, v_ref_2831_);
                lean_inc_ref(v_inheritedTraceOptions_2841_);
                lean_inc(v_cancelTk_x3f_2839_);
                lean_inc(v_currMacroScope_2837_);
                lean_inc(v_quotContext_2836_);
                lean_inc(v_maxHeartbeats_2835_);
                lean_inc(v_initHeartbeats_2834_);
                lean_inc(v_openDecls_2833_);
                lean_inc(v_currNamespace_2832_);
                lean_inc(v_maxRecDepth_2830_);
                lean_inc(v_currRecDepth_2829_);
                lean_inc_ref(v_options_2828_);
                lean_inc_ref(v_fileMap_2827_);
                lean_inc_ref(v_fileName_2826_);
                v___x_2845_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_2845_, 0, v_fileName_2826_);
                lean_ctor_set(v___x_2845_, 1, v_fileMap_2827_);
                lean_ctor_set(v___x_2845_, 2, v_options_2828_);
                lean_ctor_set(v___x_2845_, 3, v_currRecDepth_2829_);
                lean_ctor_set(v___x_2845_, 4, v_maxRecDepth_2830_);
                lean_ctor_set(v___x_2845_, 5, v_ref_2844_);
                lean_ctor_set(v___x_2845_, 6, v_currNamespace_2832_);
                lean_ctor_set(v___x_2845_, 7, v_openDecls_2833_);
                lean_ctor_set(v___x_2845_, 8, v_initHeartbeats_2834_);
                lean_ctor_set(v___x_2845_, 9, v_maxHeartbeats_2835_);
                lean_ctor_set(v___x_2845_, 10, v_quotContext_2836_);
                lean_ctor_set(v___x_2845_, 11, v_currMacroScope_2837_);
                lean_ctor_set(v___x_2845_, 12, v_cancelTk_x3f_2839_);
                lean_ctor_set(v___x_2845_, 13, v_inheritedTraceOptions_2841_);
                lean_ctor_set_uint8(
                    v___x_2845_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_2838_,
                );
                lean_ctor_set_uint8(
                    v___x_2845_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2840_,
                );
                if v___x_2843_ == 0 {
                    v___x_2846_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__5);
                    v___x_2847_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_2803_, v___x_2846_, v_a_2804_, v___x_2845_, v_a_2806_);
                    lean_dec_ref_known(v___x_2845_, 14);
                    lean_dec_ref(v_a_2804_);
                    lean_dec(v_x_2803_);
                    return v___x_2847_;
                } else {
                    v___x_2848_ = lean_unsigned_to_nat(1);
                    v___x_2849_ = l_Lean_Syntax_getArg(v_x_2803_, v___x_2848_);
                    v___x_2919_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5;
                    lean_inc(v___x_2849_);
                    v___x_2920_ = l_Lean_Syntax_isOfKind(v___x_2849_, v___x_2919_);
                    if v___x_2920_ == 0 {
                        lean_dec(v_x_2803_);
                        v___x_2921_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                        v___x_2922_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2849_, v___x_2921_, v_a_2804_, v___x_2845_, v_a_2806_);
                        lean_dec_ref_known(v___x_2845_, 14);
                        lean_dec_ref(v_a_2804_);
                        lean_dec(v___x_2849_);
                        return v___x_2922_;
                    } else {
                        v___x_2923_ = lean_unsigned_to_nat(0);
                        v___x_2924_ = l_Lean_Syntax_getArg(v___x_2849_, v___x_2923_);
                        v___x_2925_ = l_Lean_Syntax_getArgs(v___x_2924_);
                        lean_dec(v___x_2924_);
                        v___x_2926_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8;
                        v___x_2927_ = lean_array_get_size(v___x_2925_);
                        v___x_2928_ = lean_nat_dec_lt(v___x_2923_, v___x_2927_);
                        if v___x_2928_ == 0 {
                            lean_dec_ref(v___x_2925_);
                            v___y_2851_ = v___x_2926_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2929_ = lean_box((v___x_2920_) as usize);
                            v___x_2930_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2930_, 0, v___x_2929_);
                            lean_ctor_set(v___x_2930_, 1, v___x_2926_);
                            v___x_2931_ = lean_nat_dec_le(v___x_2927_, v___x_2927_);
                            if v___x_2931_ == 0 {
                                if v___x_2928_ == 0 {
                                    lean_dec_ref_known(v___x_2930_, 2);
                                    lean_dec_ref(v___x_2925_);
                                    v___y_2851_ = v___x_2926_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2932_ = 0usize;
                                    v___x_2933_ = lean_usize_of_nat(v___x_2927_);
                                    v___x_2934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2920_, v___x_2925_, v___x_2932_, v___x_2933_, v___x_2930_);
                                    lean_dec_ref(v___x_2925_);
                                    v_snd_2935_ = lean_ctor_get(v___x_2934_, 1);
                                    lean_inc(v_snd_2935_);
                                    lean_dec_ref(v___x_2934_);
                                    v___y_2851_ = v_snd_2935_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_2936_ = 0usize;
                                v___x_2937_ = lean_usize_of_nat(v___x_2927_);
                                v___x_2938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2920_, v___x_2925_, v___x_2936_, v___x_2937_, v___x_2930_);
                                lean_dec_ref(v___x_2925_);
                                v_snd_2939_ = lean_ctor_get(v___x_2938_, 1);
                                lean_inc(v_snd_2939_);
                                lean_dec_ref(v___x_2938_);
                                v___y_2851_ = v_snd_2939_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2815_ = lean_box(0);
                v___x_2816_ = 1;
                v___x_2817_ = lean_box((v___x_2816_) as usize);
                lean_inc_n(v___y_2809_, 2);
                v___x_2818_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_2809_, v___x_2817_, v_keyTys_2810_);
                v___x_2819_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
                lean_inc(v_x_2803_);
                v___x_2820_ = lean_alloc_ctor(6, 2, (0) as u32);
                lean_ctor_set(v___x_2820_, 0, v_x_2803_);
                lean_ctor_set(v___x_2820_, 1, v___x_2819_);
                v___x_2821_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2821_, 0, v_x_2803_);
                lean_ctor_set(v___x_2821_, 1, v___y_2809_);
                lean_ctor_set(v___x_2821_, 2, v___x_2820_);
                v___x_2822_ = lean_array_push(v_items_2814_, v___x_2821_);
                v___x_2823_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_2823_, 0, v___x_2818_);
                lean_ctor_set(v___x_2823_, 1, v_arrKeyTys_2811_);
                lean_ctor_set(v___x_2823_, 2, v_arrParents_2812_);
                lean_ctor_set(v___x_2823_, 3, v_currArrKey_2813_);
                lean_ctor_set(v___x_2823_, 4, v___y_2809_);
                lean_ctor_set(v___x_2823_, 5, v___x_2822_);
                v___x_2824_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2824_, 0, v___x_2815_);
                lean_ctor_set(v___x_2824_, 1, v___x_2823_);
                v___x_2825_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2825_, 0, v___x_2824_);
                return v___x_2825_;
            }
            2 => {
                v_sz_2852_ = lean_array_size(v___y_2851_);
                v___x_2853_ = 0usize;
                v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_2852_, v___x_2853_, v___y_2851_);
                if lean_obj_tag(v___x_2854_) == 0 {
                    lean_dec(v_x_2803_);
                    v___x_2855_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                    v___x_2856_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_2849_, v___x_2855_, v_a_2804_, v___x_2845_, v_a_2806_);
                    lean_dec_ref_known(v___x_2845_, 14);
                    lean_dec_ref(v_a_2804_);
                    lean_dec(v___x_2849_);
                    return v___x_2856_;
                } else {
                    lean_dec(v___x_2849_);
                    v_val_2857_ = lean_ctor_get(v___x_2854_, 0);
                    lean_inc(v_val_2857_);
                    lean_dec_ref_known(v___x_2854_, 1);
                    v___x_2858_ = lean_box(0);
                    v___x_2859_ = lean_array_get_size(v_val_2857_);
                    v___x_2860_ = lean_nat_sub(v___x_2859_, v___x_2848_);
                    v_tailKey_2861_ = lean_array_get(v___x_2858_, v_val_2857_, v___x_2860_);
                    lean_dec(v___x_2860_);
                    v___x_2862_ = lean_array_pop(v_val_2857_);
                    v___x_2863_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(
                        v___x_2862_,
                        v_a_2804_,
                        v___x_2845_,
                        v_a_2806_,
                    );
                    lean_dec_ref(v___x_2862_);
                    if lean_obj_tag(v___x_2863_) == 0 {
                        v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
                        lean_inc(v_a_2864_);
                        lean_dec_ref_known(v___x_2863_, 1);
                        v_fst_2865_ = lean_ctor_get(v_a_2864_, 0);
                        v_snd_2866_ = lean_ctor_get(v_a_2864_, 1);
                        v_isSharedCheck_2910_ = (!lean_is_exclusive(v_a_2864_)) as u8;
                        if v_isSharedCheck_2910_ == 0 {
                            v___x_2868_ = v_a_2864_;
                            v_isShared_2869_ = v_isSharedCheck_2910_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_snd_2866_);
                            lean_inc(v_fst_2865_);
                            lean_dec(v_a_2864_);
                            v___x_2868_ = lean_box(0);
                            v_isShared_2869_ = v_isSharedCheck_2910_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_tailKey_2861_);
                        lean_dec_ref_known(v___x_2845_, 14);
                        lean_dec(v_x_2803_);
                        v_a_2911_ = lean_ctor_get(v___x_2863_, 0);
                        v_isSharedCheck_2918_ = (!lean_is_exclusive(v___x_2863_)) as u8;
                        if v_isSharedCheck_2918_ == 0 {
                            v___x_2913_ = v___x_2863_;
                            v_isShared_2914_ = v_isSharedCheck_2918_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2911_);
                            lean_dec(v___x_2863_);
                            v___x_2913_ = lean_box(0);
                            v_isShared_2914_ = v_isSharedCheck_2918_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                lean_inc(v_tailKey_2861_);
                v___x_2870_ = l_Lake_Toml_elabSimpleKey(v_tailKey_2861_, v___x_2845_, v_a_2806_);
                if lean_obj_tag(v___x_2870_) == 0 {
                    v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
                    lean_inc(v_a_2871_);
                    lean_dec_ref_known(v___x_2870_, 1);
                    v_keyTys_2872_ = lean_ctor_get(v_snd_2866_, 0);
                    v_arrKeyTys_2873_ = lean_ctor_get(v_snd_2866_, 1);
                    v_arrParents_2874_ = lean_ctor_get(v_snd_2866_, 2);
                    v_currArrKey_2875_ = lean_ctor_get(v_snd_2866_, 3);
                    v_items_2876_ = lean_ctor_get(v_snd_2866_, 5);
                    v___x_2877_ = l_Lean_Name_str___override(v_fst_2865_, v_a_2871_);
                    v___x_2878_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_2872_, v___x_2877_);
                    if lean_obj_tag(v___x_2878_) == 1 {
                        v_val_2879_ = lean_ctor_get(v___x_2878_, 0);
                        v_isSharedCheck_2901_ = (!lean_is_exclusive(v___x_2878_)) as u8;
                        if v_isSharedCheck_2901_ == 0 {
                            v___x_2881_ = v___x_2878_;
                            v_isShared_2882_ = v_isSharedCheck_2901_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2879_);
                            lean_dec(v___x_2878_);
                            v___x_2881_ = lean_box(0);
                            v_isShared_2882_ = v_isSharedCheck_2901_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_inc_ref(v_items_2876_);
                        lean_inc(v_currArrKey_2875_);
                        lean_inc(v_arrParents_2874_);
                        lean_inc(v_arrKeyTys_2873_);
                        lean_inc(v_keyTys_2872_);
                        lean_dec(v___x_2878_);
                        lean_del_object(v___x_2868_);
                        lean_dec(v_snd_2866_);
                        lean_dec(v_tailKey_2861_);
                        lean_dec_ref_known(v___x_2845_, 14);
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
                    lean_del_object(v___x_2868_);
                    lean_dec(v_snd_2866_);
                    lean_dec(v_fst_2865_);
                    lean_dec(v_tailKey_2861_);
                    lean_dec_ref_known(v___x_2845_, 14);
                    lean_dec(v_x_2803_);
                    v_a_2902_ = lean_ctor_get(v___x_2870_, 0);
                    v_isSharedCheck_2909_ = (!lean_is_exclusive(v___x_2870_)) as u8;
                    if v_isSharedCheck_2909_ == 0 {
                        v___x_2904_ = v___x_2870_;
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2902_);
                        lean_dec(v___x_2870_);
                        v___x_2904_ = lean_box(0);
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2883_ = (lean_unbox(v_val_2879_) as u8);
                if v___x_2883_ == 4 {
                    lean_inc_ref(v_items_2876_);
                    lean_inc(v_currArrKey_2875_);
                    lean_inc(v_arrParents_2874_);
                    lean_inc(v_arrKeyTys_2873_);
                    lean_inc(v_keyTys_2872_);
                    lean_del_object(v___x_2881_);
                    lean_dec(v_val_2879_);
                    lean_del_object(v___x_2868_);
                    lean_dec(v_snd_2866_);
                    lean_dec(v_tailKey_2861_);
                    lean_dec_ref_known(v___x_2845_, 14);
                    v___y_2809_ = v___x_2877_;
                    v_keyTys_2810_ = v_keyTys_2872_;
                    v_arrKeyTys_2811_ = v_arrKeyTys_2873_;
                    v_arrParents_2812_ = v_arrParents_2874_;
                    v_currArrKey_2813_ = v_currArrKey_2875_;
                    v_items_2814_ = v_items_2876_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_x_2803_);
                    v___x_2884_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
                    v___x_2885_ = (lean_unbox(v_val_2879_) as u8);
                    lean_dec(v_val_2879_);
                    v___x_2886_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(
                        v___x_2885_,
                    );
                    if v_isShared_2882_ == 0 {
                        lean_ctor_set_tag(v___x_2881_, 3);
                        lean_ctor_set(v___x_2881_, 0, v___x_2886_);
                        v___x_2888_ = v___x_2881_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2900_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2886_);
                        v___x_2888_ = v_reuseFailAlloc_2900_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2889_ = l_Lean_MessageData_ofFormat(v___x_2888_);
                if v_isShared_2869_ == 0 {
                    lean_ctor_set_tag(v___x_2868_, 7);
                    lean_ctor_set(v___x_2868_, 1, v___x_2889_);
                    lean_ctor_set(v___x_2868_, 0, v___x_2884_);
                    v___x_2891_ = v___x_2868_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2899_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2884_);
                    lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2889_);
                    v___x_2891_ = v_reuseFailAlloc_2899_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2892_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
                v___x_2893_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2893_, 0, v___x_2891_);
                lean_ctor_set(v___x_2893_, 1, v___x_2892_);
                v___x_2894_ = l_Lean_MessageData_ofName(v___x_2877_);
                v___x_2895_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2895_, 0, v___x_2893_);
                lean_ctor_set(v___x_2895_, 1, v___x_2894_);
                v___x_2896_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                v___x_2897_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2897_, 0, v___x_2895_);
                lean_ctor_set(v___x_2897_, 1, v___x_2896_);
                v___x_2898_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_2861_, v___x_2897_, v_snd_2866_, v___x_2845_, v_a_2806_);
                lean_dec_ref_known(v___x_2845_, 14);
                lean_dec(v_snd_2866_);
                lean_dec(v_tailKey_2861_);
                return v___x_2898_;
            }
            7 => {
                if v_isShared_2905_ == 0 {
                    v___x_2907_ = v___x_2904_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
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
                    v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
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
    mut v_x_2940_: *mut LeanObject,
    mut v_a_2941_: *mut LeanObject,
    mut v_a_2942_: *mut LeanObject,
    mut v_a_2943_: *mut LeanObject,
    mut v_a_2944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2945_: *mut LeanObject = core::ptr::null_mut();
    v_res_2945_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(
        v_x_2940_, v_a_2941_, v_a_2942_, v_a_2943_,
    );
    lean_dec(v_a_2943_);
    lean_dec_ref(v_a_2942_);
    return v_res_2945_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3()
-> *mut LeanObject {
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    v___x_2952_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2;
    v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
    return v___x_2953_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(
    mut v_x_2954_: *mut LeanObject,
    mut v_a_2955_: *mut LeanObject,
    mut v_a_2956_: *mut LeanObject,
    mut v_a_2957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2971_: u8 = 0;
    let mut v_cancelTk_x3f_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2973_: u8 = 0;
    let mut v_inheritedTraceOptions_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: u8 = 0;
    let mut v_ref_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: u8 = 0;
    let mut v___y_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2995_: usize = 0;
    let mut v___x_2996_: usize = 0;
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tailKey_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3013_: u8 = 0;
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v_keyTys_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrKeyTys_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arrParents_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currArrKey_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3029_: u8 = 0;
    let mut v___x_3030_: u8 = 0;
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut v_unused_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3077_: u8 = 0;
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3080_: u8 = 0;
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: u8 = 0;
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3103_: u8 = 0;
    let mut v_unused_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3110_: u8 = 0;
    let mut v_a_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3114_: u8 = 0;
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3118_: u8 = 0;
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v_a_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: u8 = 0;
    let mut v___x_3139_: usize = 0;
    let mut v___x_3140_: usize = 0;
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: usize = 0;
    let mut v___x_3144_: usize = 0;
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2959_ = lean_ctor_get(v_a_2956_, 0);
                v_fileMap_2960_ = lean_ctor_get(v_a_2956_, 1);
                v_options_2961_ = lean_ctor_get(v_a_2956_, 2);
                v_currRecDepth_2962_ = lean_ctor_get(v_a_2956_, 3);
                v_maxRecDepth_2963_ = lean_ctor_get(v_a_2956_, 4);
                v_ref_2964_ = lean_ctor_get(v_a_2956_, 5);
                v_currNamespace_2965_ = lean_ctor_get(v_a_2956_, 6);
                v_openDecls_2966_ = lean_ctor_get(v_a_2956_, 7);
                v_initHeartbeats_2967_ = lean_ctor_get(v_a_2956_, 8);
                v_maxHeartbeats_2968_ = lean_ctor_get(v_a_2956_, 9);
                v_quotContext_2969_ = lean_ctor_get(v_a_2956_, 10);
                v_currMacroScope_2970_ = lean_ctor_get(v_a_2956_, 11);
                v_diag_2971_ = lean_ctor_get_uint8(
                    v_a_2956_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2972_ = lean_ctor_get(v_a_2956_, 12);
                v_suppressElabErrors_2973_ = lean_ctor_get_uint8(
                    v_a_2956_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2974_ = lean_ctor_get(v_a_2956_, 13);
                v___x_2975_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1;
                lean_inc(v_x_2954_);
                v___x_2976_ = l_Lean_Syntax_isOfKind(v_x_2954_, v___x_2975_);
                v_ref_2977_ = l_Lean_replaceRef(v_x_2954_, v_ref_2964_);
                lean_inc_ref(v_inheritedTraceOptions_2974_);
                lean_inc(v_cancelTk_x3f_2972_);
                lean_inc(v_currMacroScope_2970_);
                lean_inc(v_quotContext_2969_);
                lean_inc(v_maxHeartbeats_2968_);
                lean_inc(v_initHeartbeats_2967_);
                lean_inc(v_openDecls_2966_);
                lean_inc(v_currNamespace_2965_);
                lean_inc(v_maxRecDepth_2963_);
                lean_inc(v_currRecDepth_2962_);
                lean_inc_ref(v_options_2961_);
                lean_inc_ref(v_fileMap_2960_);
                lean_inc_ref(v_fileName_2959_);
                v___x_2978_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_2978_, 0, v_fileName_2959_);
                lean_ctor_set(v___x_2978_, 1, v_fileMap_2960_);
                lean_ctor_set(v___x_2978_, 2, v_options_2961_);
                lean_ctor_set(v___x_2978_, 3, v_currRecDepth_2962_);
                lean_ctor_set(v___x_2978_, 4, v_maxRecDepth_2963_);
                lean_ctor_set(v___x_2978_, 5, v_ref_2977_);
                lean_ctor_set(v___x_2978_, 6, v_currNamespace_2965_);
                lean_ctor_set(v___x_2978_, 7, v_openDecls_2966_);
                lean_ctor_set(v___x_2978_, 8, v_initHeartbeats_2967_);
                lean_ctor_set(v___x_2978_, 9, v_maxHeartbeats_2968_);
                lean_ctor_set(v___x_2978_, 10, v_quotContext_2969_);
                lean_ctor_set(v___x_2978_, 11, v_currMacroScope_2970_);
                lean_ctor_set(v___x_2978_, 12, v_cancelTk_x3f_2972_);
                lean_ctor_set(v___x_2978_, 13, v_inheritedTraceOptions_2974_);
                lean_ctor_set_uint8(
                    v___x_2978_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_2971_,
                );
                lean_ctor_set_uint8(
                    v___x_2978_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2973_,
                );
                if v___x_2976_ == 0 {
                    v___x_2987_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
                    v___x_2988_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_2954_, v___x_2987_, v_a_2955_, v___x_2978_, v_a_2957_);
                    lean_dec_ref_known(v___x_2978_, 14);
                    lean_dec_ref(v_a_2955_);
                    lean_dec(v_x_2954_);
                    return v___x_2988_;
                } else {
                    v___x_2989_ = lean_unsigned_to_nat(2);
                    v___x_2990_ = l_Lean_Syntax_getArg(v_x_2954_, v___x_2989_);
                    v___x_2991_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5;
                    lean_inc(v___x_2990_);
                    v___x_2992_ = l_Lean_Syntax_isOfKind(v___x_2990_, v___x_2991_);
                    if v___x_2992_ == 0 {
                        lean_dec(v___x_2990_);
                        v___x_3128_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                        v___x_3129_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_2954_, v___x_3128_, v_a_2955_, v___x_2978_, v_a_2957_);
                        lean_dec_ref_known(v___x_2978_, 14);
                        lean_dec_ref(v_a_2955_);
                        lean_dec(v_x_2954_);
                        return v___x_3129_;
                    } else {
                        v___x_3130_ = lean_unsigned_to_nat(0);
                        v___x_3131_ = l_Lean_Syntax_getArg(v___x_2990_, v___x_3130_);
                        lean_dec(v___x_2990_);
                        v___x_3132_ = l_Lean_Syntax_getArgs(v___x_3131_);
                        lean_dec(v___x_3131_);
                        v___x_3133_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8;
                        v___x_3134_ = lean_array_get_size(v___x_3132_);
                        v___x_3135_ = lean_nat_dec_lt(v___x_3130_, v___x_3134_);
                        if v___x_3135_ == 0 {
                            lean_dec_ref(v___x_3132_);
                            v___y_2994_ = v___x_3133_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3136_ = lean_box((v___x_2992_) as usize);
                            v___x_3137_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_3137_, 0, v___x_3136_);
                            lean_ctor_set(v___x_3137_, 1, v___x_3133_);
                            v___x_3138_ = lean_nat_dec_le(v___x_3134_, v___x_3134_);
                            if v___x_3138_ == 0 {
                                if v___x_3135_ == 0 {
                                    lean_dec_ref_known(v___x_3137_, 2);
                                    lean_dec_ref(v___x_3132_);
                                    v___y_2994_ = v___x_3133_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3139_ = 0usize;
                                    v___x_3140_ = lean_usize_of_nat(v___x_3134_);
                                    v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2992_, v___x_3132_, v___x_3139_, v___x_3140_, v___x_3137_);
                                    lean_dec_ref(v___x_3132_);
                                    v_snd_3142_ = lean_ctor_get(v___x_3141_, 1);
                                    lean_inc(v_snd_3142_);
                                    lean_dec_ref(v___x_3141_);
                                    v___y_2994_ = v_snd_3142_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_3143_ = 0usize;
                                v___x_3144_ = lean_usize_of_nat(v___x_3134_);
                                v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2992_, v___x_3132_, v___x_3143_, v___x_3144_, v___x_3137_);
                                lean_dec_ref(v___x_3132_);
                                v_snd_3146_ = lean_ctor_get(v___x_3145_, 1);
                                lean_inc(v_snd_3146_);
                                lean_dec_ref(v___x_3145_);
                                v___y_2994_ = v_snd_3146_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2981_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
                v___x_2982_ = l_Lean_MessageData_ofName(v___y_2980_);
                v___x_2983_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2983_, 0, v___x_2981_);
                lean_ctor_set(v___x_2983_, 1, v___x_2982_);
                v___x_2984_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
                v___x_2985_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2985_, 0, v___x_2983_);
                lean_ctor_set(v___x_2985_, 1, v___x_2984_);
                v___x_2986_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_2985_, v___x_2978_, v_a_2957_);
                lean_dec_ref_known(v___x_2978_, 14);
                return v___x_2986_;
            }
            2 => {
                v_sz_2995_ = lean_array_size(v___y_2994_);
                v___x_2996_ = 0usize;
                v___x_2997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_2995_, v___x_2996_, v___y_2994_);
                if lean_obj_tag(v___x_2997_) == 0 {
                    v___x_2998_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
                    v___x_2999_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_2954_, v___x_2998_, v_a_2955_, v___x_2978_, v_a_2957_);
                    lean_dec_ref_known(v___x_2978_, 14);
                    lean_dec_ref(v_a_2955_);
                    lean_dec(v_x_2954_);
                    return v___x_2999_;
                } else {
                    v_val_3000_ = lean_ctor_get(v___x_2997_, 0);
                    lean_inc(v_val_3000_);
                    lean_dec_ref_known(v___x_2997_, 1);
                    v___x_3001_ = lean_box(0);
                    v___x_3002_ = lean_array_get_size(v_val_3000_);
                    v___x_3003_ = lean_unsigned_to_nat(1);
                    v___x_3004_ = lean_nat_sub(v___x_3002_, v___x_3003_);
                    v_tailKey_3005_ = lean_array_get(v___x_3001_, v_val_3000_, v___x_3004_);
                    lean_dec(v___x_3004_);
                    v___x_3006_ = lean_array_pop(v_val_3000_);
                    v___x_3007_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(
                        v___x_3006_,
                        v_a_2955_,
                        v___x_2978_,
                        v_a_2957_,
                    );
                    lean_dec_ref(v___x_3006_);
                    if lean_obj_tag(v___x_3007_) == 0 {
                        v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
                        lean_inc(v_a_3008_);
                        lean_dec_ref_known(v___x_3007_, 1);
                        v_fst_3009_ = lean_ctor_get(v_a_3008_, 0);
                        v_snd_3010_ = lean_ctor_get(v_a_3008_, 1);
                        v_isSharedCheck_3119_ = (!lean_is_exclusive(v_a_3008_)) as u8;
                        if v_isSharedCheck_3119_ == 0 {
                            v___x_3012_ = v_a_3008_;
                            v_isShared_3013_ = v_isSharedCheck_3119_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_snd_3010_);
                            lean_inc(v_fst_3009_);
                            lean_dec(v_a_3008_);
                            v___x_3012_ = lean_box(0);
                            v_isShared_3013_ = v_isSharedCheck_3119_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_tailKey_3005_);
                        lean_dec_ref_known(v___x_2978_, 14);
                        lean_dec(v_x_2954_);
                        v_a_3120_ = lean_ctor_get(v___x_3007_, 0);
                        v_isSharedCheck_3127_ = (!lean_is_exclusive(v___x_3007_)) as u8;
                        if v_isSharedCheck_3127_ == 0 {
                            v___x_3122_ = v___x_3007_;
                            v_isShared_3123_ = v_isSharedCheck_3127_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3120_);
                            lean_dec(v___x_3007_);
                            v___x_3122_ = lean_box(0);
                            v_isShared_3123_ = v_isSharedCheck_3127_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            3 => {
                lean_inc(v_tailKey_3005_);
                v___x_3014_ = l_Lake_Toml_elabSimpleKey(v_tailKey_3005_, v___x_2978_, v_a_2957_);
                if lean_obj_tag(v___x_3014_) == 0 {
                    v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
                    v_isSharedCheck_3110_ = (!lean_is_exclusive(v___x_3014_)) as u8;
                    if v_isSharedCheck_3110_ == 0 {
                        v___x_3017_ = v___x_3014_;
                        v_isShared_3018_ = v_isSharedCheck_3110_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3015_);
                        lean_dec(v___x_3014_);
                        v___x_3017_ = lean_box(0);
                        v_isShared_3018_ = v_isSharedCheck_3110_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3012_);
                    lean_dec(v_snd_3010_);
                    lean_dec(v_fst_3009_);
                    lean_dec(v_tailKey_3005_);
                    lean_dec_ref_known(v___x_2978_, 14);
                    lean_dec(v_x_2954_);
                    v_a_3111_ = lean_ctor_get(v___x_3014_, 0);
                    v_isSharedCheck_3118_ = (!lean_is_exclusive(v___x_3014_)) as u8;
                    if v_isSharedCheck_3118_ == 0 {
                        v___x_3113_ = v___x_3014_;
                        v_isShared_3114_ = v_isSharedCheck_3118_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3111_);
                        lean_dec(v___x_3014_);
                        v___x_3113_ = lean_box(0);
                        v_isShared_3114_ = v_isSharedCheck_3118_;
                        state = 15;
                        continue;
                    }
                }
            }
            4 => {
                v_keyTys_3019_ = lean_ctor_get(v_snd_3010_, 0);
                v_arrKeyTys_3020_ = lean_ctor_get(v_snd_3010_, 1);
                v_arrParents_3021_ = lean_ctor_get(v_snd_3010_, 2);
                v_currArrKey_3022_ = lean_ctor_get(v_snd_3010_, 3);
                v_items_3023_ = lean_ctor_get(v_snd_3010_, 5);
                v___x_3024_ = l_Lean_Name_str___override(v_fst_3009_, v_a_3015_);
                v___x_3025_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_3019_, v___x_3024_);
                if lean_obj_tag(v___x_3025_) == 1 {
                    v_val_3026_ = lean_ctor_get(v___x_3025_, 0);
                    v_isSharedCheck_3077_ = (!lean_is_exclusive(v___x_3025_)) as u8;
                    if v_isSharedCheck_3077_ == 0 {
                        v___x_3028_ = v___x_3025_;
                        v_isShared_3029_ = v_isSharedCheck_3077_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_3026_);
                        lean_dec(v___x_3025_);
                        v___x_3028_ = lean_box(0);
                        v_isShared_3029_ = v_isSharedCheck_3077_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_items_3023_);
                    lean_inc(v_currArrKey_3022_);
                    lean_inc(v_arrParents_3021_);
                    lean_inc(v_arrKeyTys_3020_);
                    lean_inc(v_keyTys_3019_);
                    lean_dec(v___x_3025_);
                    lean_dec(v_tailKey_3005_);
                    lean_dec_ref_known(v___x_2978_, 14);
                    v_isSharedCheck_3103_ = (!lean_is_exclusive(v_snd_3010_)) as u8;
                    if v_isSharedCheck_3103_ == 0 {
                        v_unused_3104_ = lean_ctor_get(v_snd_3010_, 5);
                        lean_dec(v_unused_3104_);
                        v_unused_3105_ = lean_ctor_get(v_snd_3010_, 4);
                        lean_dec(v_unused_3105_);
                        v_unused_3106_ = lean_ctor_get(v_snd_3010_, 3);
                        lean_dec(v_unused_3106_);
                        v_unused_3107_ = lean_ctor_get(v_snd_3010_, 2);
                        lean_dec(v_unused_3107_);
                        v_unused_3108_ = lean_ctor_get(v_snd_3010_, 1);
                        lean_dec(v_unused_3108_);
                        v_unused_3109_ = lean_ctor_get(v_snd_3010_, 0);
                        lean_dec(v_unused_3109_);
                        v___x_3079_ = v_snd_3010_;
                        v_isShared_3080_ = v_isSharedCheck_3103_;
                        state = 11;
                        continue;
                    } else {
                        lean_dec(v_snd_3010_);
                        v___x_3079_ = lean_box(0);
                        v_isShared_3080_ = v_isSharedCheck_3103_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3030_ = (lean_unbox(v_val_3026_) as u8);
                if v___x_3030_ == 2 {
                    lean_inc_ref(v_items_3023_);
                    lean_inc(v_arrParents_3021_);
                    lean_inc(v_arrKeyTys_3020_);
                    lean_del_object(v___x_3028_);
                    lean_dec(v_val_3026_);
                    lean_dec(v_tailKey_3005_);
                    v_isSharedCheck_3055_ = (!lean_is_exclusive(v_snd_3010_)) as u8;
                    if v_isSharedCheck_3055_ == 0 {
                        v_unused_3056_ = lean_ctor_get(v_snd_3010_, 5);
                        lean_dec(v_unused_3056_);
                        v_unused_3057_ = lean_ctor_get(v_snd_3010_, 4);
                        lean_dec(v_unused_3057_);
                        v_unused_3058_ = lean_ctor_get(v_snd_3010_, 3);
                        lean_dec(v_unused_3058_);
                        v_unused_3059_ = lean_ctor_get(v_snd_3010_, 2);
                        lean_dec(v_unused_3059_);
                        v_unused_3060_ = lean_ctor_get(v_snd_3010_, 1);
                        lean_dec(v_unused_3060_);
                        v_unused_3061_ = lean_ctor_get(v_snd_3010_, 0);
                        lean_dec(v_unused_3061_);
                        v___x_3032_ = v_snd_3010_;
                        v_isShared_3033_ = v_isSharedCheck_3055_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v_snd_3010_);
                        v___x_3032_ = lean_box(0);
                        v_isShared_3033_ = v_isSharedCheck_3055_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3017_);
                    lean_del_object(v___x_3012_);
                    lean_dec(v_x_2954_);
                    v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0;
                    v___x_3063_ = (lean_unbox(v_val_3026_) as u8);
                    lean_dec(v_val_3026_);
                    v___x_3064_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(
                        v___x_3063_,
                    );
                    v___x_3065_ = lean_string_append(v___x_3062_, v___x_3064_);
                    lean_dec_ref(v___x_3064_);
                    v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2;
                    v___x_3067_ = lean_string_append(v___x_3065_, v___x_3066_);
                    v___x_3068_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___x_3024_,
                        v___x_2992_,
                    );
                    v___x_3069_ = lean_string_append(v___x_3067_, v___x_3068_);
                    lean_dec_ref(v___x_3068_);
                    v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4;
                    v___x_3071_ = lean_string_append(v___x_3069_, v___x_3070_);
                    if v_isShared_3029_ == 0 {
                        lean_ctor_set_tag(v___x_3028_, 3);
                        lean_ctor_set(v___x_3028_, 0, v___x_3071_);
                        v___x_3073_ = v___x_3028_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3076_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3071_);
                        v___x_3073_ = v_reuseFailAlloc_3076_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3034_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_3021_, v___x_3024_);
                if lean_obj_tag(v___x_3034_) == 0 {
                    lean_del_object(v___x_3032_);
                    lean_dec_ref(v_items_3023_);
                    lean_dec(v_arrParents_3021_);
                    lean_dec(v_arrKeyTys_3020_);
                    lean_del_object(v___x_3017_);
                    lean_del_object(v___x_3012_);
                    lean_dec(v_x_2954_);
                    v___y_2980_ = v___x_3024_;
                    state = 1;
                    continue;
                } else {
                    v_val_3035_ = lean_ctor_get(v___x_3034_, 0);
                    lean_inc(v_val_3035_);
                    lean_dec_ref_known(v___x_3034_, 1);
                    v___x_3036_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_3020_, v_val_3035_);
                    lean_dec(v_val_3035_);
                    if lean_obj_tag(v___x_3036_) == 1 {
                        lean_dec_ref_known(v___x_2978_, 14);
                        v_val_3037_ = lean_ctor_get(v___x_3036_, 0);
                        lean_inc(v_val_3037_);
                        lean_dec_ref_known(v___x_3036_, 1);
                        v___x_3038_ = lean_box(0);
                        v___x_3039_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
                        lean_inc_n(v_x_2954_, 2);
                        v___x_3040_ = lean_alloc_ctor(6, 2, (0) as u32);
                        lean_ctor_set(v___x_3040_, 0, v_x_2954_);
                        lean_ctor_set(v___x_3040_, 1, v___x_3039_);
                        v___x_3041_ = lean_mk_empty_array_with_capacity(v___x_3003_);
                        v___x_3042_ = lean_array_push(v___x_3041_, v___x_3040_);
                        v___x_3043_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_3043_, 0, v_x_2954_);
                        lean_ctor_set(v___x_3043_, 1, v___x_3042_);
                        lean_inc_n(v___x_3024_, 2);
                        v___x_3044_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_3044_, 0, v_x_2954_);
                        lean_ctor_set(v___x_3044_, 1, v___x_3024_);
                        lean_ctor_set(v___x_3044_, 2, v___x_3043_);
                        v___x_3045_ = lean_array_push(v_items_3023_, v___x_3044_);
                        if v_isShared_3033_ == 0 {
                            lean_ctor_set(v___x_3032_, 5, v___x_3045_);
                            lean_ctor_set(v___x_3032_, 4, v___x_3024_);
                            lean_ctor_set(v___x_3032_, 3, v___x_3024_);
                            lean_ctor_set(v___x_3032_, 0, v_val_3037_);
                            v___x_3047_ = v___x_3032_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 6, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_val_3037_);
                            lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_arrKeyTys_3020_);
                            lean_ctor_set(v_reuseFailAlloc_3054_, 2, v_arrParents_3021_);
                            lean_ctor_set(v_reuseFailAlloc_3054_, 3, v___x_3024_);
                            lean_ctor_set(v_reuseFailAlloc_3054_, 4, v___x_3024_);
                            lean_ctor_set(v_reuseFailAlloc_3054_, 5, v___x_3045_);
                            v___x_3047_ = v_reuseFailAlloc_3054_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3036_);
                        lean_del_object(v___x_3032_);
                        lean_dec_ref(v_items_3023_);
                        lean_dec(v_arrParents_3021_);
                        lean_dec(v_arrKeyTys_3020_);
                        lean_del_object(v___x_3017_);
                        lean_del_object(v___x_3012_);
                        lean_dec(v_x_2954_);
                        v___y_2980_ = v___x_3024_;
                        state = 1;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_3013_ == 0 {
                    lean_ctor_set(v___x_3012_, 1, v___x_3047_);
                    lean_ctor_set(v___x_3012_, 0, v___x_3038_);
                    v___x_3049_ = v___x_3012_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3038_);
                    lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_3047_);
                    v___x_3049_ = v_reuseFailAlloc_3053_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3018_ == 0 {
                    lean_ctor_set(v___x_3017_, 0, v___x_3049_);
                    v___x_3051_ = v___x_3017_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3049_);
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
                lean_dec_ref_known(v___x_2978_, 14);
                lean_dec(v_snd_3010_);
                lean_dec(v_tailKey_3005_);
                return v___x_3075_;
            }
            11 => {
                v___x_3081_ = lean_box(0);
                v___x_3082_ = 2;
                v___x_3083_ = lean_box((v___x_3082_) as usize);
                lean_inc_n(v___x_3024_, 4);
                v___x_3084_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_3024_, v___x_3083_, v_keyTys_3019_);
                lean_inc(v___x_3084_);
                lean_inc(v_currArrKey_3022_);
                v___x_3085_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_3022_, v___x_3084_, v_arrKeyTys_3020_);
                v___x_3086_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_3024_, v_currArrKey_3022_, v_arrParents_3021_);
                v___x_3087_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
                lean_inc_n(v_x_2954_, 2);
                v___x_3088_ = lean_alloc_ctor(6, 2, (0) as u32);
                lean_ctor_set(v___x_3088_, 0, v_x_2954_);
                lean_ctor_set(v___x_3088_, 1, v___x_3087_);
                v___x_3089_ = lean_mk_empty_array_with_capacity(v___x_3003_);
                v___x_3090_ = lean_array_push(v___x_3089_, v___x_3088_);
                v___x_3091_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3091_, 0, v_x_2954_);
                lean_ctor_set(v___x_3091_, 1, v___x_3090_);
                v___x_3092_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3092_, 0, v_x_2954_);
                lean_ctor_set(v___x_3092_, 1, v___x_3024_);
                lean_ctor_set(v___x_3092_, 2, v___x_3091_);
                v___x_3093_ = lean_array_push(v_items_3023_, v___x_3092_);
                if v_isShared_3080_ == 0 {
                    lean_ctor_set(v___x_3079_, 5, v___x_3093_);
                    lean_ctor_set(v___x_3079_, 4, v___x_3024_);
                    lean_ctor_set(v___x_3079_, 3, v___x_3024_);
                    lean_ctor_set(v___x_3079_, 2, v___x_3086_);
                    lean_ctor_set(v___x_3079_, 1, v___x_3085_);
                    lean_ctor_set(v___x_3079_, 0, v___x_3084_);
                    v___x_3095_ = v___x_3079_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3084_);
                    lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_3085_);
                    lean_ctor_set(v_reuseFailAlloc_3102_, 2, v___x_3086_);
                    lean_ctor_set(v_reuseFailAlloc_3102_, 3, v___x_3024_);
                    lean_ctor_set(v_reuseFailAlloc_3102_, 4, v___x_3024_);
                    lean_ctor_set(v_reuseFailAlloc_3102_, 5, v___x_3093_);
                    v___x_3095_ = v_reuseFailAlloc_3102_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3013_ == 0 {
                    lean_ctor_set(v___x_3012_, 1, v___x_3095_);
                    lean_ctor_set(v___x_3012_, 0, v___x_3081_);
                    v___x_3097_ = v___x_3012_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3081_);
                    lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3095_);
                    v___x_3097_ = v_reuseFailAlloc_3101_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3018_ == 0 {
                    lean_ctor_set(v___x_3017_, 0, v___x_3097_);
                    v___x_3099_ = v___x_3017_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
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
                    v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
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
                    v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
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
    mut v_x_3147_: *mut LeanObject,
    mut v_a_3148_: *mut LeanObject,
    mut v_a_3149_: *mut LeanObject,
    mut v_a_3150_: *mut LeanObject,
    mut v_a_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3152_: *mut LeanObject = core::ptr::null_mut();
    v_res_3152_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(
        v_x_3147_, v_a_3148_, v_a_3149_, v_a_3150_,
    );
    lean_dec(v_a_3150_);
    lean_dec_ref(v_a_3149_);
    return v_res_3152_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1()
-> *mut LeanObject {
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    v___x_3154_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0;
    v___x_3155_ = l_Lean_stringToMessageData(v___x_3154_);
    return v___x_3155_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(
    mut v_x_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
    mut v_a_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: u8 = 0;
    v___x_3161_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1;
    lean_inc(v_x_3156_);
    v___x_3162_ = l_Lean_Syntax_isOfKind(v_x_3156_, v___x_3161_);
    if v___x_3162_ == 0 {
        let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3164_: u8 = 0;
        v___x_3163_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3;
        lean_inc(v_x_3156_);
        v___x_3164_ = l_Lean_Syntax_isOfKind(v_x_3156_, v___x_3163_);
        if v___x_3164_ == 0 {
            let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3166_: u8 = 0;
            v___x_3165_ =
                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1;
            lean_inc(v_x_3156_);
            v___x_3166_ = l_Lean_Syntax_isOfKind(v_x_3156_, v___x_3165_);
            if v___x_3166_ == 0 {
                let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
                v___x_3167_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
                v___x_3168_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_3156_, v___x_3167_, v_a_3157_, v_a_3158_, v_a_3159_);
                lean_dec_ref(v_a_3157_);
                lean_dec(v_x_3156_);
                return v___x_3168_;
            } else {
                let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
                v___x_3169_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(
                    v_x_3156_, v_a_3157_, v_a_3158_, v_a_3159_,
                );
                return v___x_3169_;
            }
        } else {
            let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
            v___x_3170_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(
                v_x_3156_, v_a_3157_, v_a_3158_, v_a_3159_,
            );
            return v___x_3170_;
        }
    } else {
        let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
        v___x_3171_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(
            v_x_3156_, v_a_3157_, v_a_3158_, v_a_3159_,
        );
        return v___x_3171_;
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(
    mut v_x_3172_: *mut LeanObject,
    mut v_a_3173_: *mut LeanObject,
    mut v_a_3174_: *mut LeanObject,
    mut v_a_3175_: *mut LeanObject,
    mut v_a_3176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3177_: *mut LeanObject = core::ptr::null_mut();
    v_res_3177_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(
        v_x_3172_, v_a_3173_, v_a_3174_, v_a_3175_,
    );
    lean_dec(v_a_3175_);
    lean_dec_ref(v_a_3174_);
    return v_res_3177_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(
    mut v_ref_3178_: *mut LeanObject,
    mut v_as_3179_: *mut LeanObject,
    mut v_i_3180_: usize,
    mut v_stop_3181_: usize,
    mut v_b_3182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: usize = 0;
    let mut v___x_3186_: usize = 0;
    let mut v___x_3188_: u8 = 0;
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3188_ = lean_usize_dec_eq(v_i_3180_, v_stop_3181_);
                if v___x_3188_ == 0 {
                    v___x_3189_ = lean_array_uget_borrowed(v_as_3179_, v_i_3180_);
                    v_fst_3190_ = lean_ctor_get(v___x_3189_, 0);
                    v_snd_3191_ = lean_ctor_get(v___x_3189_, 1);
                    lean_inc(v_fst_3190_);
                    v___x_3192_ = l_Lean_Name_components(v_fst_3190_);
                    if lean_obj_tag(v___x_3192_) == 0 {
                        v___y_3184_ = v_b_3182_;
                        state = 1;
                        continue;
                    } else {
                        v_head_3193_ = lean_ctor_get(v___x_3192_, 0);
                        lean_inc(v_head_3193_);
                        v_tail_3194_ = lean_ctor_get(v___x_3192_, 1);
                        lean_inc(v_tail_3194_);
                        lean_dec_ref_known(v___x_3192_, 2);
                        lean_inc(v_snd_3191_);
                        lean_inc(v_ref_3178_);
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
                    lean_dec(v_ref_3178_);
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
    mut v_bs_3198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3199_: u8 = 0;
    let mut v_v_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: usize = 0;
    let mut v___x_3205_: usize = 0;
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3199_ = lean_usize_dec_lt(v_i_3197_, v_sz_3196_);
                if v___x_3199_ == 0 {
                    return v_bs_3198_;
                } else {
                    v_v_3200_ = lean_array_uget(v_bs_3198_, v_i_3197_);
                    v___x_3201_ = lean_unsigned_to_nat(0);
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
    mut v_a_3208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_xs_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3213_: u8 = 0;
    let mut v_items_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: u8 = 0;
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: usize = 0;
    let mut v___x_3227_: usize = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: usize = 0;
    let mut v___x_3233_: usize = 0;
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3238_: u8 = 0;
    let mut v_ref_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v_sz_3244_: usize = 0;
    let mut v___x_3245_: usize = 0;
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_3208_) {
                6 => {
                    v_xs_3209_ = lean_ctor_get(v_a_3208_, 1);
                    v_ref_3210_ = lean_ctor_get(v_a_3208_, 0);
                    v_isSharedCheck_3238_ = (!lean_is_exclusive(v_a_3208_)) as u8;
                    if v_isSharedCheck_3238_ == 0 {
                        v___x_3212_ = v_a_3208_;
                        v_isShared_3213_ = v_isSharedCheck_3238_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_xs_3209_);
                        lean_inc(v_ref_3210_);
                        lean_dec(v_a_3208_);
                        v___x_3212_ = lean_box(0);
                        v_isShared_3213_ = v_isSharedCheck_3238_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_ref_3239_ = lean_ctor_get(v_a_3208_, 0);
                    v_xs_3240_ = lean_ctor_get(v_a_3208_, 1);
                    v_isSharedCheck_3250_ = (!lean_is_exclusive(v_a_3208_)) as u8;
                    if v_isSharedCheck_3250_ == 0 {
                        v___x_3242_ = v_a_3208_;
                        v_isShared_3243_ = v_isSharedCheck_3250_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_xs_3240_);
                        lean_inc(v_ref_3239_);
                        lean_dec(v_a_3208_);
                        v___x_3242_ = lean_box(0);
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
                v_items_3214_ = lean_ctor_get(v_xs_3209_, 0);
                lean_inc_ref(v_items_3214_);
                lean_dec_ref(v_xs_3209_);
                v___x_3215_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once), _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1);
                v___x_3216_ = lean_unsigned_to_nat(0);
                v___x_3217_ = lean_array_get_size(v_items_3214_);
                v___x_3218_ = lean_nat_dec_lt(v___x_3216_, v___x_3217_);
                if v___x_3218_ == 0 {
                    lean_dec_ref(v_items_3214_);
                    if v_isShared_3213_ == 0 {
                        lean_ctor_set(v___x_3212_, 1, v___x_3215_);
                        v___x_3220_ = v___x_3212_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3221_ = lean_alloc_ctor(6, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_ref_3210_);
                        lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___x_3215_);
                        v___x_3220_ = v_reuseFailAlloc_3221_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3222_ = lean_nat_dec_le(v___x_3217_, v___x_3217_);
                    if v___x_3222_ == 0 {
                        if v___x_3218_ == 0 {
                            lean_dec_ref(v_items_3214_);
                            if v_isShared_3213_ == 0 {
                                lean_ctor_set(v___x_3212_, 1, v___x_3215_);
                                v___x_3224_ = v___x_3212_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3225_ = lean_alloc_ctor(6, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_ref_3210_);
                                lean_ctor_set(v_reuseFailAlloc_3225_, 1, v___x_3215_);
                                v___x_3224_ = v_reuseFailAlloc_3225_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_3226_ = 0usize;
                            v___x_3227_ = lean_usize_of_nat(v___x_3217_);
                            lean_inc(v_ref_3210_);
                            v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_3210_, v_items_3214_, v___x_3226_, v___x_3227_, v___x_3215_);
                            lean_dec_ref(v_items_3214_);
                            if v_isShared_3213_ == 0 {
                                lean_ctor_set(v___x_3212_, 1, v___x_3228_);
                                v___x_3230_ = v___x_3212_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3231_ = lean_alloc_ctor(6, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_ref_3210_);
                                lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3228_);
                                v___x_3230_ = v_reuseFailAlloc_3231_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_3232_ = 0usize;
                        v___x_3233_ = lean_usize_of_nat(v___x_3217_);
                        lean_inc(v_ref_3210_);
                        v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_3210_, v_items_3214_, v___x_3232_, v___x_3233_, v___x_3215_);
                        lean_dec_ref(v_items_3214_);
                        if v_isShared_3213_ == 0 {
                            lean_ctor_set(v___x_3212_, 1, v___x_3234_);
                            v___x_3236_ = v___x_3212_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3237_ = lean_alloc_ctor(6, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_ref_3210_);
                            lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3234_);
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
                    lean_ctor_set(v___x_3242_, 1, v___x_3246_);
                    v___x_3248_ = v___x_3242_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3249_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_ref_3239_);
                    lean_ctor_set(v_reuseFailAlloc_3249_, 1, v___x_3246_);
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
    mut v_newV_3251_: *mut LeanObject,
    mut v___x_3252_: *mut LeanObject,
    mut v_v_x3f_3253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v_items_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3267_: u8 = 0;
    let mut v_unused_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3278_: u8 = 0;
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3283_: u8 = 0;
    let mut v_unused_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3289_: u8 = 0;
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_x3f_3253_) == 1 {
                    v_val_3254_ = lean_ctor_get(v_v_x3f_3253_, 0);
                    lean_inc(v_val_3254_);
                    lean_dec_ref_known(v_v_x3f_3253_, 1);
                    match lean_obj_tag(v_val_3254_) {
                        6 => {
                            v_ref_3255_ = lean_ctor_get(v_val_3254_, 0);
                            lean_inc(v_ref_3255_);
                            v_xs_3256_ = lean_ctor_get(v_val_3254_, 1);
                            lean_inc_ref(v_xs_3256_);
                            lean_dec_ref_known(v_val_3254_, 2);
                            v___x_3257_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_3251_);
                            if lean_obj_tag(v___x_3257_) == 6 {
                                v_xs_3258_ = lean_ctor_get(v___x_3257_, 1);
                                v_isSharedCheck_3267_ = (!lean_is_exclusive(v___x_3257_)) as u8;
                                if v_isSharedCheck_3267_ == 0 {
                                    v_unused_3268_ = lean_ctor_get(v___x_3257_, 0);
                                    lean_dec(v_unused_3268_);
                                    v___x_3260_ = v___x_3257_;
                                    v_isShared_3261_ = v_isSharedCheck_3267_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_xs_3258_);
                                    lean_dec(v___x_3257_);
                                    v___x_3260_ = lean_box(0);
                                    v_isShared_3261_ = v_isSharedCheck_3267_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_xs_3256_);
                                lean_dec(v_ref_3255_);
                                lean_dec_ref(v___x_3252_);
                                return v___x_3257_;
                            }
                        }
                        5 => {
                            lean_dec_ref(v___x_3252_);
                            v_ref_3269_ = lean_ctor_get(v_val_3254_, 0);
                            v_xs_3270_ = lean_ctor_get(v_val_3254_, 1);
                            v_isSharedCheck_3289_ = (!lean_is_exclusive(v_val_3254_)) as u8;
                            if v_isSharedCheck_3289_ == 0 {
                                v___x_3272_ = v_val_3254_;
                                v_isShared_3273_ = v_isSharedCheck_3289_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_xs_3270_);
                                lean_inc(v_ref_3269_);
                                lean_dec(v_val_3254_);
                                v___x_3272_ = lean_box(0);
                                v_isShared_3273_ = v_isSharedCheck_3289_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            lean_dec(v_val_3254_);
                            lean_dec_ref(v___x_3252_);
                            v___x_3290_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_3251_);
                            return v___x_3290_;
                        }
                    }
                } else {
                    lean_dec(v_v_x3f_3253_);
                    lean_dec_ref(v___x_3252_);
                    v___x_3291_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(
                            v_newV_3251_,
                        );
                    return v___x_3291_;
                }
            }
            1 => {
                v_items_3262_ = lean_ctor_get(v_xs_3258_, 0);
                lean_inc_ref(v_items_3262_);
                lean_dec_ref(v_xs_3258_);
                v___x_3263_ =
                    l_Lake_Toml_RBDict_appendArray___redArg(v___x_3252_, v_xs_3256_, v_items_3262_);
                lean_dec_ref(v_items_3262_);
                if v_isShared_3261_ == 0 {
                    lean_ctor_set(v___x_3260_, 1, v___x_3263_);
                    lean_ctor_set(v___x_3260_, 0, v_ref_3255_);
                    v___x_3265_ = v___x_3260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3266_ = lean_alloc_ctor(6, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_ref_3255_);
                    lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3263_);
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
                if lean_obj_tag(v___x_3274_) == 5 {
                    lean_del_object(v___x_3272_);
                    v_xs_3275_ = lean_ctor_get(v___x_3274_, 1);
                    v_isSharedCheck_3283_ = (!lean_is_exclusive(v___x_3274_)) as u8;
                    if v_isSharedCheck_3283_ == 0 {
                        v_unused_3284_ = lean_ctor_get(v___x_3274_, 0);
                        lean_dec(v_unused_3284_);
                        v___x_3277_ = v___x_3274_;
                        v_isShared_3278_ = v_isSharedCheck_3283_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_xs_3275_);
                        lean_dec(v___x_3274_);
                        v___x_3277_ = lean_box(0);
                        v_isShared_3278_ = v_isSharedCheck_3283_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_3285_ = lean_array_push(v_xs_3270_, v___x_3274_);
                    if v_isShared_3273_ == 0 {
                        lean_ctor_set(v___x_3272_, 1, v___x_3285_);
                        v___x_3287_ = v___x_3272_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3288_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_ref_3269_);
                        lean_ctor_set(v_reuseFailAlloc_3288_, 1, v___x_3285_);
                        v___x_3287_ = v_reuseFailAlloc_3288_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3279_ = l_Array_append___redArg(v_xs_3270_, v_xs_3275_);
                lean_dec_ref(v_xs_3275_);
                if v_isShared_3278_ == 0 {
                    lean_ctor_set(v___x_3277_, 1, v___x_3279_);
                    lean_ctor_set(v___x_3277_, 0, v_ref_3269_);
                    v___x_3281_ = v___x_3277_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3282_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_ref_3269_);
                    lean_ctor_set(v_reuseFailAlloc_3282_, 1, v___x_3279_);
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
    mut v_newV_3292_: *mut LeanObject,
    mut v_k_3293_: *mut LeanObject,
    mut v_t_3294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3300_: u8 = 0;
    let mut v_items_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: u8 = 0;
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3316_: u8 = 0;
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3330_: u8 = 0;
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3295_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0;
                lean_inc_ref(v_t_3294_);
                lean_inc(v_k_3293_);
                v___x_3296_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_3295_, v_k_3293_, v_t_3294_);
                if lean_obj_tag(v___x_3296_) == 1 {
                    lean_dec(v_k_3293_);
                    v_val_3297_ = lean_ctor_get(v___x_3296_, 0);
                    v_isSharedCheck_3332_ = (!lean_is_exclusive(v___x_3296_)) as u8;
                    if v_isSharedCheck_3332_ == 0 {
                        v___x_3299_ = v___x_3296_;
                        v_isShared_3300_ = v_isSharedCheck_3332_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3297_);
                        lean_dec(v___x_3296_);
                        v___x_3299_ = lean_box(0);
                        v_isShared_3300_ = v_isSharedCheck_3332_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3296_);
                    v___x_3333_ = lean_box(0);
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
                v_items_3301_ = lean_ctor_get(v_t_3294_, 0);
                v_indices_3302_ = lean_ctor_get(v_t_3294_, 1);
                v_isSharedCheck_3331_ = (!lean_is_exclusive(v_t_3294_)) as u8;
                if v_isSharedCheck_3331_ == 0 {
                    v___x_3304_ = v_t_3294_;
                    v_isShared_3305_ = v_isSharedCheck_3331_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_indices_3302_);
                    lean_inc(v_items_3301_);
                    lean_dec(v_t_3294_);
                    v___x_3304_ = lean_box(0);
                    v_isShared_3305_ = v_isSharedCheck_3331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3306_ = lean_array_get_size(v_items_3301_);
                v___x_3307_ = lean_nat_dec_lt(v_val_3297_, v___x_3306_);
                if v___x_3307_ == 0 {
                    lean_del_object(v___x_3299_);
                    lean_dec(v_val_3297_);
                    lean_dec_ref(v_newV_3292_);
                    if v_isShared_3305_ == 0 {
                        v___x_3309_ = v___x_3304_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_items_3301_);
                        lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_indices_3302_);
                        v___x_3309_ = v_reuseFailAlloc_3310_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_v_3311_ = lean_array_fget(v_items_3301_, v_val_3297_);
                    v_fst_3312_ = lean_ctor_get(v_v_3311_, 0);
                    v_snd_3313_ = lean_ctor_get(v_v_3311_, 1);
                    v_isSharedCheck_3330_ = (!lean_is_exclusive(v_v_3311_)) as u8;
                    if v_isSharedCheck_3330_ == 0 {
                        v___x_3315_ = v_v_3311_;
                        v_isShared_3316_ = v_isSharedCheck_3330_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_3313_);
                        lean_inc(v_fst_3312_);
                        lean_dec(v_v_3311_);
                        v___x_3315_ = lean_box(0);
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
                v___x_3317_ = lean_box(0);
                v_xs_x27_3318_ = lean_array_fset(v_items_3301_, v_val_3297_, v___x_3317_);
                if v_isShared_3300_ == 0 {
                    lean_ctor_set(v___x_3299_, 0, v_snd_3313_);
                    v___x_3320_ = v___x_3299_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_snd_3313_);
                    v___x_3320_ = v_reuseFailAlloc_3329_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3321_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_3292_, v___x_3295_, v___x_3320_);
                if v_isShared_3316_ == 0 {
                    lean_ctor_set(v___x_3315_, 1, v___x_3321_);
                    v___x_3323_ = v___x_3315_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_fst_3312_);
                    lean_ctor_set(v_reuseFailAlloc_3328_, 1, v___x_3321_);
                    v___x_3323_ = v_reuseFailAlloc_3328_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3324_ = lean_array_fset(v_xs_x27_3318_, v_val_3297_, v___x_3323_);
                lean_dec(v_val_3297_);
                if v_isShared_3305_ == 0 {
                    lean_ctor_set(v___x_3304_, 0, v___x_3324_);
                    v___x_3326_ = v___x_3304_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
                    lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_indices_3302_);
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
    mut v_kRef_3336_: *mut LeanObject,
    mut v_head_3337_: *mut LeanObject,
    mut v_tail_3338_: *mut LeanObject,
    mut v_newV_3339_: *mut LeanObject,
    mut v___x_3340_: *mut LeanObject,
    mut v_v_x3f_3341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: u8 = 0;
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3351_: u8 = 0;
    let mut v_v_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3365_: u8 = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3373_: u8 = 0;
    let mut v_unused_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3385_: u8 = 0;
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_x3f_3341_) == 1 {
                    v_val_3342_ = lean_ctor_get(v_v_x3f_3341_, 0);
                    lean_inc(v_val_3342_);
                    lean_dec_ref_known(v_v_x3f_3341_, 1);
                    match lean_obj_tag(v_val_3342_) {
                        5 => {
                            v_ref_3343_ = lean_ctor_get(v_val_3342_, 0);
                            v_xs_3344_ = lean_ctor_get(v_val_3342_, 1);
                            v___x_3345_ = lean_array_get_size(v_xs_3344_);
                            v___x_3346_ = lean_unsigned_to_nat(1);
                            v___x_3347_ = lean_nat_sub(v___x_3345_, v___x_3346_);
                            v___x_3348_ = lean_nat_dec_lt(v___x_3347_, v___x_3345_);
                            if v___x_3348_ == 0 {
                                lean_dec(v___x_3347_);
                                lean_dec_ref(v_newV_3339_);
                                lean_dec(v_tail_3338_);
                                lean_dec(v_head_3337_);
                                lean_dec(v_kRef_3336_);
                                return v_val_3342_;
                            } else {
                                lean_inc_ref(v_xs_3344_);
                                lean_inc(v_ref_3343_);
                                v_isSharedCheck_3373_ = (!lean_is_exclusive(v_val_3342_)) as u8;
                                if v_isSharedCheck_3373_ == 0 {
                                    v_unused_3374_ = lean_ctor_get(v_val_3342_, 1);
                                    lean_dec(v_unused_3374_);
                                    v_unused_3375_ = lean_ctor_get(v_val_3342_, 0);
                                    lean_dec(v_unused_3375_);
                                    v___x_3350_ = v_val_3342_;
                                    v_isShared_3351_ = v_isSharedCheck_3373_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_val_3342_);
                                    v___x_3350_ = lean_box(0);
                                    v_isShared_3351_ = v_isSharedCheck_3373_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        6 => {
                            v_ref_3376_ = lean_ctor_get(v_val_3342_, 0);
                            v_xs_3377_ = lean_ctor_get(v_val_3342_, 1);
                            v_isSharedCheck_3385_ = (!lean_is_exclusive(v_val_3342_)) as u8;
                            if v_isSharedCheck_3385_ == 0 {
                                v___x_3379_ = v_val_3342_;
                                v_isShared_3380_ = v_isSharedCheck_3385_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_xs_3377_);
                                lean_inc(v_ref_3376_);
                                lean_dec(v_val_3342_);
                                v___x_3379_ = lean_box(0);
                                v_isShared_3380_ = v_isSharedCheck_3385_;
                                state = 6;
                                continue;
                            }
                        }
                        _ => {
                            lean_dec(v_val_3342_);
                            v___x_3386_ =
                                l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_3340_);
                            lean_inc(v_kRef_3336_);
                            v___x_3387_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_3386_, v_kRef_3336_, v_head_3337_, v_tail_3338_, v_newV_3339_);
                            v___x_3388_ = lean_alloc_ctor(6, 2, (0) as u32);
                            lean_ctor_set(v___x_3388_, 0, v_kRef_3336_);
                            lean_ctor_set(v___x_3388_, 1, v___x_3387_);
                            return v___x_3388_;
                        }
                    }
                } else {
                    lean_dec(v_v_x3f_3341_);
                    v___x_3389_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_3340_);
                    lean_inc(v_kRef_3336_);
                    v___x_3390_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(
                            v___x_3389_,
                            v_kRef_3336_,
                            v_head_3337_,
                            v_tail_3338_,
                            v_newV_3339_,
                        );
                    v___x_3391_ = lean_alloc_ctor(6, 2, (0) as u32);
                    lean_ctor_set(v___x_3391_, 0, v_kRef_3336_);
                    lean_ctor_set(v___x_3391_, 1, v___x_3390_);
                    return v___x_3391_;
                }
            }
            1 => {
                v_v_3352_ = lean_array_fget(v_xs_3344_, v___x_3347_);
                v___x_3353_ = lean_box(0);
                v_xs_x27_3354_ = lean_array_fset(v_xs_3344_, v___x_3347_, v___x_3353_);
                if lean_obj_tag(v_v_3352_) == 6 {
                    v_ref_3361_ = lean_ctor_get(v_v_3352_, 0);
                    v_xs_3362_ = lean_ctor_get(v_v_3352_, 1);
                    v_isSharedCheck_3370_ = (!lean_is_exclusive(v_v_3352_)) as u8;
                    if v_isSharedCheck_3370_ == 0 {
                        v___x_3364_ = v_v_3352_;
                        v_isShared_3365_ = v_isSharedCheck_3370_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_xs_3362_);
                        lean_inc(v_ref_3361_);
                        lean_dec(v_v_3352_);
                        v___x_3364_ = lean_box(0);
                        v_isShared_3365_ = v_isSharedCheck_3370_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_v_3352_);
                    lean_dec_ref(v_newV_3339_);
                    lean_dec(v_tail_3338_);
                    lean_dec(v_head_3337_);
                    v___x_3371_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_3340_);
                    v___x_3372_ = lean_alloc_ctor(6, 2, (0) as u32);
                    lean_ctor_set(v___x_3372_, 0, v_kRef_3336_);
                    lean_ctor_set(v___x_3372_, 1, v___x_3371_);
                    v___y_3356_ = v___x_3372_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3357_ = lean_array_fset(v_xs_x27_3354_, v___x_3347_, v___y_3356_);
                lean_dec(v___x_3347_);
                if v_isShared_3351_ == 0 {
                    lean_ctor_set(v___x_3350_, 1, v___x_3357_);
                    v___x_3359_ = v___x_3350_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3360_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_ref_3343_);
                    lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___x_3357_);
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
                    lean_ctor_set(v___x_3364_, 1, v___x_3366_);
                    v___x_3368_ = v___x_3364_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3369_ = lean_alloc_ctor(6, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_ref_3361_);
                    lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3366_);
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
                    lean_ctor_set(v___x_3379_, 1, v___x_3381_);
                    v___x_3383_ = v___x_3379_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3384_ = lean_alloc_ctor(6, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_ref_3376_);
                    lean_ctor_set(v_reuseFailAlloc_3384_, 1, v___x_3381_);
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
    mut v_kRef_3392_: *mut LeanObject,
    mut v_head_3393_: *mut LeanObject,
    mut v_tail_3394_: *mut LeanObject,
    mut v_newV_3395_: *mut LeanObject,
    mut v_k_3396_: *mut LeanObject,
    mut v_t_3397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v_items_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indices_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3408_: u8 = 0;
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: u8 = 0;
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3419_: u8 = 0;
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3433_: u8 = 0;
    let mut v_isSharedCheck_3434_: u8 = 0;
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3398_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0;
                lean_inc_ref(v_t_3397_);
                lean_inc(v_k_3396_);
                v___x_3399_ =
                    l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_3398_, v_k_3396_, v_t_3397_);
                if lean_obj_tag(v___x_3399_) == 1 {
                    lean_dec(v_k_3396_);
                    v_val_3400_ = lean_ctor_get(v___x_3399_, 0);
                    v_isSharedCheck_3435_ = (!lean_is_exclusive(v___x_3399_)) as u8;
                    if v_isSharedCheck_3435_ == 0 {
                        v___x_3402_ = v___x_3399_;
                        v_isShared_3403_ = v_isSharedCheck_3435_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3400_);
                        lean_dec(v___x_3399_);
                        v___x_3402_ = lean_box(0);
                        v_isShared_3403_ = v_isSharedCheck_3435_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3399_);
                    v___x_3436_ = lean_box(0);
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
                v_items_3404_ = lean_ctor_get(v_t_3397_, 0);
                v_indices_3405_ = lean_ctor_get(v_t_3397_, 1);
                v_isSharedCheck_3434_ = (!lean_is_exclusive(v_t_3397_)) as u8;
                if v_isSharedCheck_3434_ == 0 {
                    v___x_3407_ = v_t_3397_;
                    v_isShared_3408_ = v_isSharedCheck_3434_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_indices_3405_);
                    lean_inc(v_items_3404_);
                    lean_dec(v_t_3397_);
                    v___x_3407_ = lean_box(0);
                    v_isShared_3408_ = v_isSharedCheck_3434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3409_ = lean_array_get_size(v_items_3404_);
                v___x_3410_ = lean_nat_dec_lt(v_val_3400_, v___x_3409_);
                if v___x_3410_ == 0 {
                    lean_del_object(v___x_3402_);
                    lean_dec(v_val_3400_);
                    lean_dec_ref(v_newV_3395_);
                    lean_dec(v_tail_3394_);
                    lean_dec(v_head_3393_);
                    lean_dec(v_kRef_3392_);
                    if v_isShared_3408_ == 0 {
                        v___x_3412_ = v___x_3407_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_items_3404_);
                        lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_indices_3405_);
                        v___x_3412_ = v_reuseFailAlloc_3413_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_v_3414_ = lean_array_fget(v_items_3404_, v_val_3400_);
                    v_fst_3415_ = lean_ctor_get(v_v_3414_, 0);
                    v_snd_3416_ = lean_ctor_get(v_v_3414_, 1);
                    v_isSharedCheck_3433_ = (!lean_is_exclusive(v_v_3414_)) as u8;
                    if v_isSharedCheck_3433_ == 0 {
                        v___x_3418_ = v_v_3414_;
                        v_isShared_3419_ = v_isSharedCheck_3433_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_3416_);
                        lean_inc(v_fst_3415_);
                        lean_dec(v_v_3414_);
                        v___x_3418_ = lean_box(0);
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
                v___x_3420_ = lean_box(0);
                v_xs_x27_3421_ = lean_array_fset(v_items_3404_, v_val_3400_, v___x_3420_);
                if v_isShared_3403_ == 0 {
                    lean_ctor_set(v___x_3402_, 0, v_snd_3416_);
                    v___x_3423_ = v___x_3402_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_snd_3416_);
                    v___x_3423_ = v_reuseFailAlloc_3432_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3424_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_3392_, v_head_3393_, v_tail_3394_, v_newV_3395_, v___x_3398_, v___x_3423_);
                if v_isShared_3419_ == 0 {
                    lean_ctor_set(v___x_3418_, 1, v___x_3424_);
                    v___x_3426_ = v___x_3418_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_fst_3415_);
                    lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3424_);
                    v___x_3426_ = v_reuseFailAlloc_3431_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3427_ = lean_array_fset(v_xs_x27_3421_, v_val_3400_, v___x_3426_);
                lean_dec(v_val_3400_);
                if v_isShared_3408_ == 0 {
                    lean_ctor_set(v___x_3407_, 0, v___x_3427_);
                    v___x_3429_ = v___x_3407_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
                    lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_indices_3405_);
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
    mut v_t_3439_: *mut LeanObject,
    mut v_kRef_3440_: *mut LeanObject,
    mut v_k_3441_: *mut LeanObject,
    mut v_ks_3442_: *mut LeanObject,
    mut v_newV_3443_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_ks_3442_) == 0 {
        let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_kRef_3440_);
        v___x_3444_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_3443_, v_k_3441_, v_t_3439_);
        return v___x_3444_;
    } else {
        let mut v_head_3445_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_3446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
        v_head_3445_ = lean_ctor_get(v_ks_3442_, 0);
        lean_inc(v_head_3445_);
        v_tail_3446_ = lean_ctor_get(v_ks_3442_, 1);
        lean_inc(v_tail_3446_);
        lean_dec_ref_known(v_ks_3442_, 2);
        v___x_3447_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_3440_, v_head_3445_, v_tail_3446_, v_newV_3443_, v_k_3441_, v_t_3439_);
        return v___x_3447_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(
    mut v_sz_3448_: *mut LeanObject,
    mut v_i_3449_: *mut LeanObject,
    mut v_bs_3450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3451_: usize = 0;
    let mut v_i_boxed_3452_: usize = 0;
    let mut v_res_3453_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3451_ = lean_unbox_usize(v_sz_3448_);
    lean_dec(v_sz_3448_);
    v_i_boxed_3452_ = lean_unbox_usize(v_i_3449_);
    lean_dec(v_i_3449_);
    v_res_3453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_3451_, v_i_boxed_3452_, v_bs_3450_);
    return v_res_3453_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(
    mut v_ref_3454_: *mut LeanObject,
    mut v_as_3455_: *mut LeanObject,
    mut v_i_3456_: *mut LeanObject,
    mut v_stop_3457_: *mut LeanObject,
    mut v_b_3458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3459_: usize = 0;
    let mut v_stop_boxed_3460_: usize = 0;
    let mut v_res_3461_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3459_ = lean_unbox_usize(v_i_3456_);
    lean_dec(v_i_3456_);
    v_stop_boxed_3460_ = lean_unbox_usize(v_stop_3457_);
    lean_dec(v_stop_3457_);
    v_res_3461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_3454_, v_as_3455_, v_i_boxed_3459_, v_stop_boxed_3460_, v_b_3458_);
    lean_dec_ref(v_as_3455_);
    return v_res_3461_;
}
pub unsafe fn l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0___boxed(
    mut v_kRef_3462_: *mut LeanObject,
    mut v_head_3463_: *mut LeanObject,
    mut v_tail_3464_: *mut LeanObject,
    mut v_newV_3465_: *mut LeanObject,
    mut v___x_3466_: *mut LeanObject,
    mut v_v_x3f_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3468_: *mut LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_3462_, v_head_3463_, v_tail_3464_, v_newV_3465_, v___x_3466_, v_v_x3f_3467_);
    lean_dec_ref(v___x_3466_);
    return v_res_3468_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(
    mut v_as_3469_: *mut LeanObject,
    mut v_i_3470_: usize,
    mut v_stop_3471_: usize,
    mut v_b_3472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: usize = 0;
    let mut v___x_3476_: usize = 0;
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3478_ = lean_usize_dec_eq(v_i_3470_, v_stop_3471_);
                if v___x_3478_ == 0 {
                    v___x_3479_ = lean_array_uget_borrowed(v_as_3469_, v_i_3470_);
                    v_ref_3480_ = lean_ctor_get(v___x_3479_, 0);
                    v_key_3481_ = lean_ctor_get(v___x_3479_, 1);
                    v_val_3482_ = lean_ctor_get(v___x_3479_, 2);
                    lean_inc(v_key_3481_);
                    v___x_3483_ = l_Lean_Name_components(v_key_3481_);
                    if lean_obj_tag(v___x_3483_) == 0 {
                        v___y_3474_ = v_b_3472_;
                        state = 1;
                        continue;
                    } else {
                        v_head_3484_ = lean_ctor_get(v___x_3483_, 0);
                        lean_inc(v_head_3484_);
                        v_tail_3485_ = lean_ctor_get(v___x_3483_, 1);
                        lean_inc(v_tail_3485_);
                        lean_dec_ref_known(v___x_3483_, 2);
                        lean_inc_ref(v_val_3482_);
                        lean_inc(v_ref_3480_);
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
    mut v_as_3487_: *mut LeanObject,
    mut v_i_3488_: *mut LeanObject,
    mut v_stop_3489_: *mut LeanObject,
    mut v_b_3490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3491_: usize = 0;
    let mut v_stop_boxed_3492_: usize = 0;
    let mut v_res_3493_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3491_ = lean_unbox_usize(v_i_3488_);
    lean_dec(v_i_3488_);
    v_stop_boxed_3492_ = lean_unbox_usize(v_stop_3489_);
    lean_dec(v_stop_3489_);
    v_res_3493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_3487_, v_i_boxed_3491_, v_stop_boxed_3492_, v_b_3490_);
    lean_dec_ref(v_as_3487_);
    return v_res_3493_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(
    mut v_items_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    v___x_3495_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_once
        ),
        _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1,
    );
    v___x_3496_ = lean_unsigned_to_nat(0);
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
                let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
                v___x_3500_ = 0usize;
                v___x_3501_ = lean_usize_of_nat(v___x_3497_);
                v___x_3502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_3494_, v___x_3500_, v___x_3501_, v___x_3495_);
                return v___x_3502_;
            }
        } else {
            let mut v___x_3503_: usize = 0;
            let mut v___x_3504_: usize = 0;
            let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
            v___x_3503_ = 0usize;
            v___x_3504_ = lean_usize_of_nat(v___x_3497_);
            v___x_3505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_3494_, v___x_3503_, v___x_3504_, v___x_3495_);
            return v___x_3505_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(
    mut v_items_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3507_: *mut LeanObject = core::ptr::null_mut();
    v_res_3507_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_3506_);
    lean_dec_ref(v_items_3506_);
    return v_res_3507_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(
    mut v_x_3508_: *mut LeanObject,
    mut v_a_3509_: *mut LeanObject,
    mut v_a_3510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3517_: u8 = 0;
    let mut v_snd_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3524_: u8 = 0;
    let mut v_a_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3532_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3512_ = l_Lake_Toml_instInhabitedElabState_default___closed__1;
                lean_inc(v_a_3510_);
                lean_inc_ref(v_a_3509_);
                v___x_3513_ =
                    lean_apply_4(v_x_3508_, v___x_3512_, v_a_3509_, v_a_3510_, lean_box(0));
                if lean_obj_tag(v___x_3513_) == 0 {
                    v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
                    v_isSharedCheck_3524_ = (!lean_is_exclusive(v___x_3513_)) as u8;
                    if v_isSharedCheck_3524_ == 0 {
                        v___x_3516_ = v___x_3513_;
                        v_isShared_3517_ = v_isSharedCheck_3524_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3514_);
                        lean_dec(v___x_3513_);
                        v___x_3516_ = lean_box(0);
                        v_isShared_3517_ = v_isSharedCheck_3524_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3525_ = lean_ctor_get(v___x_3513_, 0);
                    v_isSharedCheck_3532_ = (!lean_is_exclusive(v___x_3513_)) as u8;
                    if v_isSharedCheck_3532_ == 0 {
                        v___x_3527_ = v___x_3513_;
                        v_isShared_3528_ = v_isSharedCheck_3532_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3525_);
                        lean_dec(v___x_3513_);
                        v___x_3527_ = lean_box(0);
                        v_isShared_3528_ = v_isSharedCheck_3532_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3518_ = lean_ctor_get(v_a_3514_, 1);
                lean_inc(v_snd_3518_);
                lean_dec(v_a_3514_);
                v_items_3519_ = lean_ctor_get(v_snd_3518_, 5);
                lean_inc_ref(v_items_3519_);
                lean_dec(v_snd_3518_);
                v___x_3520_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_3519_);
                lean_dec_ref(v_items_3519_);
                if v_isShared_3517_ == 0 {
                    lean_ctor_set(v___x_3516_, 0, v___x_3520_);
                    v___x_3522_ = v___x_3516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
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
                    v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
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
    mut v_x_3533_: *mut LeanObject,
    mut v_a_3534_: *mut LeanObject,
    mut v_a_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3537_: *mut LeanObject = core::ptr::null_mut();
    v_res_3537_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(
        v_x_3533_, v_a_3534_, v_a_3535_,
    );
    lean_dec(v_a_3535_);
    lean_dec_ref(v_a_3534_);
    return v_res_3537_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(
    mut v___y_3546_: u8,
    mut v_suppressElabErrors_3547_: u8,
    mut v_x_3548_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3548_) == 1 {
        let mut v_pre_3549_: *mut LeanObject = core::ptr::null_mut();
        v_pre_3549_ = lean_ctor_get(v_x_3548_, 0);
        match lean_obj_tag(v_pre_3549_) {
            1 => {
                let mut v_pre_3550_: *mut LeanObject = core::ptr::null_mut();
                v_pre_3550_ = lean_ctor_get(v_pre_3549_, 0);
                match lean_obj_tag(v_pre_3550_) {
                    0 => {
                        let mut v_str_3551_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_3552_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3554_: u8 = 0;
                        v_str_3551_ = lean_ctor_get(v_x_3548_, 1);
                        v_str_3552_ = lean_ctor_get(v_pre_3549_, 1);
                        v___x_3553_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0;
                        v___x_3554_ = lean_string_dec_eq(v_str_3552_, v___x_3553_);
                        if v___x_3554_ == 0 {
                            let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3556_: u8 = 0;
                            v___x_3555_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1;
                            v___x_3556_ = lean_string_dec_eq(v_str_3552_, v___x_3555_);
                            if v___x_3556_ == 0 {
                                return v___y_3546_;
                            } else {
                                let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_3561_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_3561_ = lean_ctor_get(v_pre_3550_, 0);
                        if lean_obj_tag(v_pre_3561_) == 0 {
                            let mut v_str_3562_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_3563_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_3564_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3566_: u8 = 0;
                            v_str_3562_ = lean_ctor_get(v_x_3548_, 1);
                            v_str_3563_ = lean_ctor_get(v_pre_3549_, 1);
                            v_str_3564_ = lean_ctor_get(v_pre_3550_, 1);
                            v___x_3565_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4;
                            v___x_3566_ = lean_string_dec_eq(v_str_3564_, v___x_3565_);
                            if v___x_3566_ == 0 {
                                return v___y_3546_;
                            } else {
                                let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_3568_: u8 = 0;
                                v___x_3567_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5;
                                v___x_3568_ = lean_string_dec_eq(v_str_3563_, v___x_3567_);
                                if v___x_3568_ == 0 {
                                    return v___y_3546_;
                                } else {
                                    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_3571_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3573_: u8 = 0;
                v_str_3571_ = lean_ctor_get(v_x_3548_, 1);
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
    mut v___y_3574_: *mut LeanObject,
    mut v_suppressElabErrors_3575_: *mut LeanObject,
    mut v_x_3576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_11747__boxed_3577_: u8 = 0;
    let mut v_suppressElabErrors_boxed_3578_: u8 = 0;
    let mut v_res_3579_: u8 = 0;
    let mut v_r_3580_: *mut LeanObject = core::ptr::null_mut();
    v___y_11747__boxed_3577_ = (lean_unbox(v___y_3574_) as u8);
    v_suppressElabErrors_boxed_3578_ = (lean_unbox(v_suppressElabErrors_3575_) as u8);
    v_res_3579_ =
        l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(
            v___y_11747__boxed_3577_,
            v_suppressElabErrors_boxed_3578_,
            v_x_3576_,
        );
    lean_dec(v_x_3576_);
    v_r_3580_ = lean_box((v_res_3579_) as usize);
    return v_r_3580_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(
    mut v_opts_3581_: *mut LeanObject,
    mut v_opt_3582_: *mut LeanObject,
) -> u8 {
    let mut v_name_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    v_name_3583_ = lean_ctor_get(v_opt_3582_, 0);
    v_defValue_3584_ = lean_ctor_get(v_opt_3582_, 1);
    v_map_3585_ = lean_ctor_get(v_opts_3581_, 0);
    v___x_3586_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3585_,
            v_name_3583_,
        );
    if lean_obj_tag(v___x_3586_) == 0 {
        let mut v___x_3587_: u8 = 0;
        v___x_3587_ = (lean_unbox(v_defValue_3584_) as u8);
        return v___x_3587_;
    } else {
        let mut v_val_3588_: *mut LeanObject = core::ptr::null_mut();
        v_val_3588_ = lean_ctor_get(v___x_3586_, 0);
        lean_inc(v_val_3588_);
        lean_dec_ref_known(v___x_3586_, 1);
        if lean_obj_tag(v_val_3588_) == 1 {
            let mut v_v_3589_: u8 = 0;
            v_v_3589_ = lean_ctor_get_uint8(v_val_3588_, 0 as u32);
            lean_dec_ref_known(v_val_3588_, 0);
            return v_v_3589_;
        } else {
            let mut v___x_3590_: u8 = 0;
            lean_dec(v_val_3588_);
            v___x_3590_ = (lean_unbox(v_defValue_3584_) as u8);
            return v___x_3590_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(
    mut v_opts_3591_: *mut LeanObject,
    mut v_opt_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3593_: u8 = 0;
    let mut v_r_3594_: *mut LeanObject = core::ptr::null_mut();
    v_res_3593_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_3591_, v_opt_3592_);
    lean_dec_ref(v_opt_3592_);
    lean_dec_ref(v_opts_3591_);
    v_r_3594_ = lean_box((v_res_3593_) as usize);
    return v_r_3594_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(
    mut v_ref_3596_: *mut LeanObject,
    mut v_msgData_3597_: *mut LeanObject,
    mut v_severity_3598_: u8,
    mut v_isSilent_3599_: u8,
    mut v___y_3600_: *mut LeanObject,
    mut v___y_3601_: *mut LeanObject,
    mut v___y_3602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3614_: u8 = 0;
    let mut v___y_3615_: u8 = 0;
    let mut v___y_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3632_: u8 = 0;
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut v___y_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3645_: u8 = 0;
    let mut v___y_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3649_: u8 = 0;
    let mut v___y_3650_: u8 = 0;
    let mut v___y_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: u8 = 0;
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3666_: u8 = 0;
    let mut v___y_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3669_: u8 = 0;
    let mut v___y_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3673_: u8 = 0;
    let mut v___y_3674_: u8 = 0;
    let mut v___y_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3680_: u8 = 0;
    let mut v___y_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3684_: u8 = 0;
    let mut v___y_3685_: u8 = 0;
    let mut v_ref_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: u8 = 0;
    let mut v___y_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3693_: u8 = 0;
    let mut v___y_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3697_: u8 = 0;
    let mut v___y_3698_: u8 = 0;
    let mut v___y_3700_: u8 = 0;
    let mut v_fileName_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3705_: u8 = 0;
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: u8 = 0;
    let mut v___x_3710_: u8 = 0;
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: u8 = 0;
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_3597_);
                    v___x_3717_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3597_);
                    v___y_3700_ = v___x_3717_;
                    state = 11;
                    continue;
                }
            }
            1 => {
                v___x_3606_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3606_, 0, v_a_3605_);
                lean_ctor_set(v___x_3606_, 1, v___y_3600_);
                v___x_3607_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3607_, 0, v___x_3606_);
                return v___x_3607_;
            }
            2 => {
                v___x_3618_ = lean_st_ref_take(v___y_3617_);
                v_currNamespace_3619_ = lean_ctor_get(v___y_3616_, 6);
                v_openDecls_3620_ = lean_ctor_get(v___y_3616_, 7);
                v_env_3621_ = lean_ctor_get(v___x_3618_, 0);
                v_nextMacroScope_3622_ = lean_ctor_get(v___x_3618_, 1);
                v_ngen_3623_ = lean_ctor_get(v___x_3618_, 2);
                v_auxDeclNGen_3624_ = lean_ctor_get(v___x_3618_, 3);
                v_traceState_3625_ = lean_ctor_get(v___x_3618_, 4);
                v_cache_3626_ = lean_ctor_get(v___x_3618_, 5);
                v_messages_3627_ = lean_ctor_get(v___x_3618_, 6);
                v_infoState_3628_ = lean_ctor_get(v___x_3618_, 7);
                v_snapshotTasks_3629_ = lean_ctor_get(v___x_3618_, 8);
                v_isSharedCheck_3642_ = (!lean_is_exclusive(v___x_3618_)) as u8;
                if v_isSharedCheck_3642_ == 0 {
                    v___x_3631_ = v___x_3618_;
                    v_isShared_3632_ = v_isSharedCheck_3642_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3629_);
                    lean_inc(v_infoState_3628_);
                    lean_inc(v_messages_3627_);
                    lean_inc(v_cache_3626_);
                    lean_inc(v_traceState_3625_);
                    lean_inc(v_auxDeclNGen_3624_);
                    lean_inc(v_ngen_3623_);
                    lean_inc(v_nextMacroScope_3622_);
                    lean_inc(v_env_3621_);
                    lean_dec(v___x_3618_);
                    v___x_3631_ = lean_box(0);
                    v_isShared_3632_ = v_isSharedCheck_3642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_openDecls_3620_);
                lean_inc(v_currNamespace_3619_);
                v___x_3633_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3633_, 0, v_currNamespace_3619_);
                lean_ctor_set(v___x_3633_, 1, v_openDecls_3620_);
                v___x_3634_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3634_, 0, v___x_3633_);
                lean_ctor_set(v___x_3634_, 1, v___y_3612_);
                lean_inc_ref(v___y_3613_);
                lean_inc_ref(v___y_3611_);
                v___x_3635_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_3635_, 0, v___y_3611_);
                lean_ctor_set(v___x_3635_, 1, v___y_3610_);
                lean_ctor_set(v___x_3635_, 2, v___y_3609_);
                lean_ctor_set(v___x_3635_, 3, v___y_3613_);
                lean_ctor_set(v___x_3635_, 4, v___x_3634_);
                lean_ctor_set_uint8(
                    v___x_3635_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_3615_,
                );
                lean_ctor_set_uint8(
                    v___x_3635_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_3614_,
                );
                lean_ctor_set_uint8(
                    v___x_3635_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3599_,
                );
                v___x_3636_ = l_Lean_MessageLog_add(v___x_3635_, v_messages_3627_);
                if v_isShared_3632_ == 0 {
                    lean_ctor_set(v___x_3631_, 6, v___x_3636_);
                    v___x_3638_ = v___x_3631_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_env_3621_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_nextMacroScope_3622_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_ngen_3623_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_auxDeclNGen_3624_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 4, v_traceState_3625_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 5, v_cache_3626_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 6, v___x_3636_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 7, v_infoState_3628_);
                    lean_ctor_set(v_reuseFailAlloc_3641_, 8, v_snapshotTasks_3629_);
                    v___x_3638_ = v_reuseFailAlloc_3641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3639_ = lean_st_ref_set(v___y_3617_, v___x_3638_);
                v___x_3640_ = lean_box(0);
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
                v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
                v_isSharedCheck_3666_ = (!lean_is_exclusive(v___x_3653_)) as u8;
                if v_isSharedCheck_3666_ == 0 {
                    v___x_3656_ = v___x_3653_;
                    v_isShared_3657_ = v_isSharedCheck_3666_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_a_3654_);
                    lean_dec(v___x_3653_);
                    v___x_3656_ = lean_box(0);
                    v_isShared_3657_ = v_isSharedCheck_3666_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc_ref_n(v___y_3647_, 2);
                v___x_3658_ = l_Lean_FileMap_toPosition(v___y_3647_, v___y_3646_);
                lean_dec(v___y_3646_);
                v___x_3659_ = l_Lean_FileMap_toPosition(v___y_3647_, v___y_3651_);
                lean_dec(v___y_3651_);
                if v_isShared_3657_ == 0 {
                    lean_ctor_set_tag(v___x_3656_, 1);
                    lean_ctor_set(v___x_3656_, 0, v___x_3659_);
                    v___x_3661_ = v___x_3656_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3659_);
                    v___x_3661_ = v_reuseFailAlloc_3665_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3662_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0;
                if v___y_3645_ == 0 {
                    lean_dec_ref(v___y_3644_);
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
                    lean_inc(v_a_3654_);
                    v___x_3663_ = l_Lean_MessageData_hasTag(v___y_3644_, v_a_3654_);
                    if v___x_3663_ == 0 {
                        lean_dec_ref(v___x_3661_);
                        lean_dec_ref(v___x_3658_);
                        lean_dec(v_a_3654_);
                        v___x_3664_ = lean_box(0);
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
                lean_dec(v___y_3672_);
                if lean_obj_tag(v___x_3676_) == 0 {
                    lean_inc(v___y_3675_);
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
                    v_val_3677_ = lean_ctor_get(v___x_3676_, 0);
                    lean_inc(v_val_3677_);
                    lean_dec_ref_known(v___x_3676_, 1);
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
                if lean_obj_tag(v___x_3687_) == 0 {
                    v___x_3688_ = lean_unsigned_to_nat(0);
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
                    v_val_3689_ = lean_ctor_get(v___x_3687_, 0);
                    lean_inc(v_val_3689_);
                    lean_dec_ref_known(v___x_3687_, 1);
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
                    v_fileName_3701_ = lean_ctor_get(v___y_3601_, 0);
                    v_fileMap_3702_ = lean_ctor_get(v___y_3601_, 1);
                    v_options_3703_ = lean_ctor_get(v___y_3601_, 2);
                    v_ref_3704_ = lean_ctor_get(v___y_3601_, 5);
                    v_suppressElabErrors_3705_ = lean_ctor_get_uint8(
                        v___y_3601_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3706_ = lean_box((v___y_3700_) as usize);
                    v___x_3707_ = lean_box((v_suppressElabErrors_3705_) as usize);
                    v___f_3708_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_3708_, 0, v___x_3706_);
                    lean_closure_set(v___f_3708_, 1, v___x_3707_);
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
                    lean_dec_ref(v_msgData_3597_);
                    v___x_3713_ = lean_box(0);
                    v___x_3714_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3714_, 0, v___x_3713_);
                    lean_ctor_set(v___x_3714_, 1, v___y_3600_);
                    v___x_3715_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3715_, 0, v___x_3714_);
                    return v___x_3715_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(
    mut v_ref_3718_: *mut LeanObject,
    mut v_msgData_3719_: *mut LeanObject,
    mut v_severity_3720_: *mut LeanObject,
    mut v_isSilent_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_3726_: u8 = 0;
    let mut v_isSilent_boxed_3727_: u8 = 0;
    let mut v_res_3728_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_3726_ = (lean_unbox(v_severity_3720_) as u8);
    v_isSilent_boxed_3727_ = (lean_unbox(v_isSilent_3721_) as u8);
    v_res_3728_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(
        v_ref_3718_,
        v_msgData_3719_,
        v_severity_boxed_3726_,
        v_isSilent_boxed_3727_,
        v___y_3722_,
        v___y_3723_,
        v___y_3724_,
    );
    lean_dec(v___y_3724_);
    lean_dec_ref(v___y_3723_);
    lean_dec(v_ref_3718_);
    return v_res_3728_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(
    mut v_ref_3729_: *mut LeanObject,
    mut v_msgData_3730_: *mut LeanObject,
    mut v___y_3731_: *mut LeanObject,
    mut v___y_3732_: *mut LeanObject,
    mut v___y_3733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3735_: u8 = 0;
    let mut v___x_3736_: u8 = 0;
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_ref_3738_: *mut LeanObject,
    mut v_msgData_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
    mut v___y_3742_: *mut LeanObject,
    mut v___y_3743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3744_: *mut LeanObject = core::ptr::null_mut();
    v_res_3744_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(
        v_ref_3738_,
        v_msgData_3739_,
        v___y_3740_,
        v___y_3741_,
        v___y_3742_,
    );
    lean_dec(v___y_3742_);
    lean_dec_ref(v___y_3741_);
    lean_dec(v_ref_3738_);
    return v_res_3744_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    v___x_3747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0;
    v___x_3748_ = l_Lean_MessageData_ofFormat(v___x_3747_);
    return v___x_3748_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(
    mut v_recovering_3749_: u8,
    mut v_as_3750_: *mut LeanObject,
    mut v_sz_3751_: usize,
    mut v_i_3752_: usize,
    mut v_b_3753_: u8,
    mut v___y_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: usize = 0;
    let mut v___x_3762_: usize = 0;
    let mut v___x_3763_: u8 = 0;
    let mut v___y_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: u8 = 0;
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3787_: u8 = 0;
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recovering_3793_: u8 = 0;
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: u8 = 0;
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3787_ = lean_usize_dec_lt(v_i_3752_, v_sz_3751_);
                if v___x_3787_ == 0 {
                    v___x_3788_ = lean_box((v_b_3753_) as usize);
                    v___x_3789_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3789_, 0, v___x_3788_);
                    lean_ctor_set(v___x_3789_, 1, v___y_3754_);
                    v___x_3790_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3790_, 0, v___x_3789_);
                    return v___x_3790_;
                } else {
                    v_a_3791_ = lean_array_uget_borrowed(v_as_3750_, v_i_3752_);
                    v___x_3792_ =
                        l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1;
                    lean_inc(v_a_3791_);
                    v_recovering_3793_ = l_Lean_Syntax_isOfKind(v_a_3791_, v___x_3792_);
                    if v_recovering_3793_ == 0 {
                        v___x_3794_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3;
                        lean_inc(v_a_3791_);
                        v___x_3795_ = l_Lean_Syntax_isOfKind(v_a_3791_, v___x_3794_);
                        if v___x_3795_ == 0 {
                            v___x_3796_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1;
                            lean_inc(v_a_3791_);
                            v___x_3797_ = l_Lean_Syntax_isOfKind(v_a_3791_, v___x_3796_);
                            if v___x_3797_ == 0 {
                                v___x_3798_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
                                lean_inc_ref(v___y_3754_);
                                v___x_3799_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(
                                    v_a_3791_,
                                    v___x_3798_,
                                    v___y_3754_,
                                    v___y_3755_,
                                    v___y_3756_,
                                );
                                if lean_obj_tag(v___x_3799_) == 0 {
                                    lean_dec_ref(v___y_3754_);
                                    v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
                                    lean_inc(v_a_3800_);
                                    lean_dec_ref_known(v___x_3799_, 1);
                                    v_snd_3801_ = lean_ctor_get(v_a_3800_, 1);
                                    lean_inc(v_snd_3801_);
                                    lean_dec(v_a_3800_);
                                    v___x_3802_ = lean_box((v_b_3753_) as usize);
                                    v_snd_3759_ = v___x_3802_;
                                    v_snd_3760_ = v_snd_3801_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_3803_ = lean_ctor_get(v___x_3799_, 0);
                                    lean_inc(v_a_3803_);
                                    lean_dec_ref_known(v___x_3799_, 1);
                                    v_a_3784_ = v_a_3803_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_inc_ref(v___y_3754_);
                                lean_inc(v_a_3791_);
                                v___x_3804_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_3791_, v___y_3754_, v___y_3755_, v___y_3756_);
                                if lean_obj_tag(v___x_3804_) == 0 {
                                    lean_dec_ref(v___y_3754_);
                                    v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
                                    lean_inc(v_a_3805_);
                                    lean_dec_ref_known(v___x_3804_, 1);
                                    v_snd_3806_ = lean_ctor_get(v_a_3805_, 1);
                                    lean_inc(v_snd_3806_);
                                    lean_dec(v_a_3805_);
                                    v___x_3807_ = lean_box((v_recovering_3793_) as usize);
                                    v_snd_3759_ = v___x_3807_;
                                    v_snd_3760_ = v_snd_3806_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_3808_ = lean_ctor_get(v___x_3804_, 0);
                                    lean_inc(v_a_3808_);
                                    lean_dec_ref_known(v___x_3804_, 1);
                                    v_a_3784_ = v_a_3808_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc_ref(v___y_3754_);
                            lean_inc(v_a_3791_);
                            v___x_3809_ =
                                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(
                                    v_a_3791_,
                                    v___y_3754_,
                                    v___y_3755_,
                                    v___y_3756_,
                                );
                            if lean_obj_tag(v___x_3809_) == 0 {
                                lean_dec_ref(v___y_3754_);
                                v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
                                lean_inc(v_a_3810_);
                                lean_dec_ref_known(v___x_3809_, 1);
                                v_snd_3811_ = lean_ctor_get(v_a_3810_, 1);
                                lean_inc(v_snd_3811_);
                                lean_dec(v_a_3810_);
                                v___x_3812_ = lean_box((v_recovering_3793_) as usize);
                                v_snd_3759_ = v___x_3812_;
                                v_snd_3760_ = v_snd_3811_;
                                state = 1;
                                continue;
                            } else {
                                v_a_3813_ = lean_ctor_get(v___x_3809_, 0);
                                lean_inc(v_a_3813_);
                                lean_dec_ref_known(v___x_3809_, 1);
                                v_a_3784_ = v_a_3813_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        if v_b_3753_ == 0 {
                            lean_inc_ref(v___y_3754_);
                            lean_inc(v_a_3791_);
                            v___x_3814_ =
                                l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(
                                    v_a_3791_,
                                    v___y_3754_,
                                    v___y_3755_,
                                    v___y_3756_,
                                );
                            if lean_obj_tag(v___x_3814_) == 0 {
                                lean_dec_ref(v___y_3754_);
                                v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
                                lean_inc(v_a_3815_);
                                lean_dec_ref_known(v___x_3814_, 1);
                                v_snd_3816_ = lean_ctor_get(v_a_3815_, 1);
                                lean_inc(v_snd_3816_);
                                lean_dec(v_a_3815_);
                                v___x_3817_ = lean_box((v_b_3753_) as usize);
                                v_snd_3759_ = v___x_3817_;
                                v_snd_3760_ = v_snd_3816_;
                                state = 1;
                                continue;
                            } else {
                                v_a_3818_ = lean_ctor_get(v___x_3814_, 0);
                                lean_inc(v_a_3818_);
                                lean_dec_ref_known(v___x_3814_, 1);
                                v_a_3784_ = v_a_3818_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___x_3819_ = lean_box((v_b_3753_) as usize);
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
                v___x_3763_ = (lean_unbox(v_snd_3759_) as u8);
                lean_dec(v_snd_3759_);
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
                    lean_dec(v___x_3768_);
                    if lean_obj_tag(v___x_3770_) == 0 {
                        v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
                        lean_inc(v_a_3771_);
                        lean_dec_ref_known(v___x_3770_, 1);
                        v_snd_3772_ = lean_ctor_get(v_a_3771_, 1);
                        lean_inc(v_snd_3772_);
                        lean_dec(v_a_3771_);
                        v___x_3773_ = lean_box((v_recovering_3749_) as usize);
                        v_snd_3759_ = v___x_3773_;
                        v_snd_3760_ = v_snd_3772_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3774_ = lean_ctor_get(v___x_3770_, 0);
                        v_isSharedCheck_3781_ = (!lean_is_exclusive(v___x_3770_)) as u8;
                        if v_isSharedCheck_3781_ == 0 {
                            v___x_3776_ = v___x_3770_;
                            v_isShared_3777_ = v_isSharedCheck_3781_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3774_);
                            lean_dec(v___x_3770_);
                            v___x_3776_ = lean_box(0);
                            v_isShared_3777_ = v_isSharedCheck_3781_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3754_);
                    v___x_3782_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3782_, 0, v___y_3766_);
                    return v___x_3782_;
                }
            }
            3 => {
                if v_isShared_3777_ == 0 {
                    v___x_3779_ = v___x_3776_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
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
                    lean_inc_ref(v_a_3784_);
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
    mut v_recovering_3820_: *mut LeanObject,
    mut v_as_3821_: *mut LeanObject,
    mut v_sz_3822_: *mut LeanObject,
    mut v_i_3823_: *mut LeanObject,
    mut v_b_3824_: *mut LeanObject,
    mut v___y_3825_: *mut LeanObject,
    mut v___y_3826_: *mut LeanObject,
    mut v___y_3827_: *mut LeanObject,
    mut v___y_3828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_recovering_boxed_3829_: u8 = 0;
    let mut v_sz_boxed_3830_: usize = 0;
    let mut v_i_boxed_3831_: usize = 0;
    let mut v_b_boxed_3832_: u8 = 0;
    let mut v_res_3833_: *mut LeanObject = core::ptr::null_mut();
    v_recovering_boxed_3829_ = (lean_unbox(v_recovering_3820_) as u8);
    v_sz_boxed_3830_ = lean_unbox_usize(v_sz_3822_);
    lean_dec(v_sz_3822_);
    v_i_boxed_3831_ = lean_unbox_usize(v_i_3823_);
    lean_dec(v_i_3823_);
    v_b_boxed_3832_ = (lean_unbox(v_b_3824_) as u8);
    v_res_3833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_3829_, v_as_3821_, v_sz_boxed_3830_, v_i_boxed_3831_, v_b_boxed_3832_, v___y_3825_, v___y_3826_, v___y_3827_);
    lean_dec(v___y_3827_);
    lean_dec_ref(v___y_3826_);
    lean_dec_ref(v_as_3821_);
    return v_res_3833_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(
    mut v_msg_3834_: *mut LeanObject,
    mut v___y_3835_: *mut LeanObject,
    mut v___y_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3838_ = lean_ctor_get(v___y_3835_, 5);
                v___x_3839_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_3834_, v___y_3835_, v___y_3836_);
                v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
                v_isSharedCheck_3848_ = (!lean_is_exclusive(v___x_3839_)) as u8;
                if v_isSharedCheck_3848_ == 0 {
                    v___x_3842_ = v___x_3839_;
                    v_isShared_3843_ = v_isSharedCheck_3848_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3840_);
                    lean_dec(v___x_3839_);
                    v___x_3842_ = lean_box(0);
                    v_isShared_3843_ = v_isSharedCheck_3848_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3838_);
                v___x_3844_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3844_, 0, v_ref_3838_);
                lean_ctor_set(v___x_3844_, 1, v_a_3840_);
                if v_isShared_3843_ == 0 {
                    lean_ctor_set_tag(v___x_3842_, 1);
                    lean_ctor_set(v___x_3842_, 0, v___x_3844_);
                    v___x_3846_ = v___x_3842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
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
    mut v_msg_3849_: *mut LeanObject,
    mut v___y_3850_: *mut LeanObject,
    mut v___y_3851_: *mut LeanObject,
    mut v___y_3852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3853_: *mut LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_3849_, v___y_3850_, v___y_3851_);
    lean_dec(v___y_3851_);
    lean_dec_ref(v___y_3850_);
    return v_res_3853_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(
    mut v_ref_3854_: *mut LeanObject,
    mut v_msg_3855_: *mut LeanObject,
    mut v___y_3856_: *mut LeanObject,
    mut v___y_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3871_: u8 = 0;
    let mut v_cancelTk_x3f_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3873_: u8 = 0;
    let mut v_inheritedTraceOptions_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3859_ = lean_ctor_get(v___y_3856_, 0);
    v_fileMap_3860_ = lean_ctor_get(v___y_3856_, 1);
    v_options_3861_ = lean_ctor_get(v___y_3856_, 2);
    v_currRecDepth_3862_ = lean_ctor_get(v___y_3856_, 3);
    v_maxRecDepth_3863_ = lean_ctor_get(v___y_3856_, 4);
    v_ref_3864_ = lean_ctor_get(v___y_3856_, 5);
    v_currNamespace_3865_ = lean_ctor_get(v___y_3856_, 6);
    v_openDecls_3866_ = lean_ctor_get(v___y_3856_, 7);
    v_initHeartbeats_3867_ = lean_ctor_get(v___y_3856_, 8);
    v_maxHeartbeats_3868_ = lean_ctor_get(v___y_3856_, 9);
    v_quotContext_3869_ = lean_ctor_get(v___y_3856_, 10);
    v_currMacroScope_3870_ = lean_ctor_get(v___y_3856_, 11);
    v_diag_3871_ = lean_ctor_get_uint8(
        v___y_3856_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3872_ = lean_ctor_get(v___y_3856_, 12);
    v_suppressElabErrors_3873_ = lean_ctor_get_uint8(
        v___y_3856_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3874_ = lean_ctor_get(v___y_3856_, 13);
    v_ref_3875_ = l_Lean_replaceRef(v_ref_3854_, v_ref_3864_);
    lean_inc_ref(v_inheritedTraceOptions_3874_);
    lean_inc(v_cancelTk_x3f_3872_);
    lean_inc(v_currMacroScope_3870_);
    lean_inc(v_quotContext_3869_);
    lean_inc(v_maxHeartbeats_3868_);
    lean_inc(v_initHeartbeats_3867_);
    lean_inc(v_openDecls_3866_);
    lean_inc(v_currNamespace_3865_);
    lean_inc(v_maxRecDepth_3863_);
    lean_inc(v_currRecDepth_3862_);
    lean_inc_ref(v_options_3861_);
    lean_inc_ref(v_fileMap_3860_);
    lean_inc_ref(v_fileName_3859_);
    v___x_3876_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3876_, 0, v_fileName_3859_);
    lean_ctor_set(v___x_3876_, 1, v_fileMap_3860_);
    lean_ctor_set(v___x_3876_, 2, v_options_3861_);
    lean_ctor_set(v___x_3876_, 3, v_currRecDepth_3862_);
    lean_ctor_set(v___x_3876_, 4, v_maxRecDepth_3863_);
    lean_ctor_set(v___x_3876_, 5, v_ref_3875_);
    lean_ctor_set(v___x_3876_, 6, v_currNamespace_3865_);
    lean_ctor_set(v___x_3876_, 7, v_openDecls_3866_);
    lean_ctor_set(v___x_3876_, 8, v_initHeartbeats_3867_);
    lean_ctor_set(v___x_3876_, 9, v_maxHeartbeats_3868_);
    lean_ctor_set(v___x_3876_, 10, v_quotContext_3869_);
    lean_ctor_set(v___x_3876_, 11, v_currMacroScope_3870_);
    lean_ctor_set(v___x_3876_, 12, v_cancelTk_x3f_3872_);
    lean_ctor_set(v___x_3876_, 13, v_inheritedTraceOptions_3874_);
    lean_ctor_set_uint8(
        v___x_3876_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3871_,
    );
    lean_ctor_set_uint8(
        v___x_3876_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3873_,
    );
    v___x_3877_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_3855_, v___x_3876_, v___y_3857_);
    lean_dec_ref_known(v___x_3876_, 14);
    return v___x_3877_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(
    mut v_ref_3878_: *mut LeanObject,
    mut v_msg_3879_: *mut LeanObject,
    mut v___y_3880_: *mut LeanObject,
    mut v___y_3881_: *mut LeanObject,
    mut v___y_3882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3883_: *mut LeanObject = core::ptr::null_mut();
    v_res_3883_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(
        v_ref_3878_,
        v_msg_3879_,
        v___y_3880_,
        v___y_3881_,
    );
    lean_dec(v___y_3881_);
    lean_dec_ref(v___y_3880_);
    lean_dec(v_ref_3878_);
    return v_res_3883_;
}
pub unsafe fn _init_l_Lake_Toml_elabToml___closed__3() -> *mut LeanObject {
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    v___x_3890_ = l_Lake_Toml_elabToml___closed__2;
    v___x_3891_ = l_Lean_stringToMessageData(v___x_3890_);
    return v___x_3891_;
}
pub unsafe fn l_Lake_Toml_elabToml(
    mut v_x_3896_: *mut LeanObject,
    mut v_a_3897_: *mut LeanObject,
    mut v_a_3898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recovering_3907_: u8 = 0;
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recovering_3913_: u8 = 0;
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3915_: usize = 0;
    let mut v___x_3916_: usize = 0;
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v_snd_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3929_: u8 = 0;
    let mut v_a_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3933_: u8 = 0;
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3900_ = l_Lake_Toml_elabToml___closed__1;
                lean_inc(v_x_3896_);
                v___x_3901_ = l_Lean_Syntax_isOfKind(v_x_3896_, v___x_3900_);
                if v___x_3901_ == 0 {
                    v___x_3902_ = lean_obj_once(
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
                    lean_dec(v_x_3896_);
                    return v___x_3903_;
                } else {
                    v___x_3904_ = lean_unsigned_to_nat(0);
                    v___x_3905_ = l_Lean_Syntax_getArg(v_x_3896_, v___x_3904_);
                    v___x_3906_ = l_Lake_Toml_elabToml___closed__4;
                    v_recovering_3907_ = l_Lean_Syntax_isOfKind(v___x_3905_, v___x_3906_);
                    if v_recovering_3907_ == 0 {
                        v___x_3908_ = lean_obj_once(
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
                        lean_dec(v_x_3896_);
                        return v___x_3909_;
                    } else {
                        v___x_3910_ = lean_unsigned_to_nat(1);
                        v___x_3911_ = l_Lean_Syntax_getArg(v_x_3896_, v___x_3910_);
                        lean_dec(v_x_3896_);
                        v_xs_3912_ = l_Lean_Syntax_getArgs(v___x_3911_);
                        lean_dec(v___x_3911_);
                        v_recovering_3913_ = 0;
                        v___x_3914_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_3912_);
                        lean_dec_ref(v_xs_3912_);
                        v_sz_3915_ = lean_array_size(v___x_3914_);
                        v___x_3916_ = 0usize;
                        v___x_3917_ = l_Lake_Toml_instInhabitedElabState_default___closed__1;
                        v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_3907_, v___x_3914_, v_sz_3915_, v___x_3916_, v_recovering_3913_, v___x_3917_, v_a_3897_, v_a_3898_);
                        lean_dec_ref(v___x_3914_);
                        if lean_obj_tag(v___x_3918_) == 0 {
                            v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
                            v_isSharedCheck_3929_ = (!lean_is_exclusive(v___x_3918_)) as u8;
                            if v_isSharedCheck_3929_ == 0 {
                                v___x_3921_ = v___x_3918_;
                                v_isShared_3922_ = v_isSharedCheck_3929_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3919_);
                                lean_dec(v___x_3918_);
                                v___x_3921_ = lean_box(0);
                                v_isShared_3922_ = v_isSharedCheck_3929_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3930_ = lean_ctor_get(v___x_3918_, 0);
                            v_isSharedCheck_3937_ = (!lean_is_exclusive(v___x_3918_)) as u8;
                            if v_isSharedCheck_3937_ == 0 {
                                v___x_3932_ = v___x_3918_;
                                v_isShared_3933_ = v_isSharedCheck_3937_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3930_);
                                lean_dec(v___x_3918_);
                                v___x_3932_ = lean_box(0);
                                v_isShared_3933_ = v_isSharedCheck_3937_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_snd_3923_ = lean_ctor_get(v_a_3919_, 1);
                lean_inc(v_snd_3923_);
                lean_dec(v_a_3919_);
                v_items_3924_ = lean_ctor_get(v_snd_3923_, 5);
                lean_inc_ref(v_items_3924_);
                lean_dec(v_snd_3923_);
                v___x_3925_ =
                    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_3924_);
                lean_dec_ref(v_items_3924_);
                if v_isShared_3922_ == 0 {
                    lean_ctor_set(v___x_3921_, 0, v___x_3925_);
                    v___x_3927_ = v___x_3921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3925_);
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
                    v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
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
    mut v_x_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
    mut v_a_3941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3942_: *mut LeanObject = core::ptr::null_mut();
    v_res_3942_ = l_Lake_Toml_elabToml(v_x_3938_, v_a_3939_, v_a_3940_);
    lean_dec(v_a_3940_);
    lean_dec_ref(v_a_3939_);
    return v_res_3942_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(
    mut v_00_u03b1_3943_: *mut LeanObject,
    mut v_ref_3944_: *mut LeanObject,
    mut v_msg_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
    mut v___y_3947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    v___x_3949_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(
        v_ref_3944_,
        v_msg_3945_,
        v___y_3946_,
        v___y_3947_,
    );
    return v___x_3949_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(
    mut v_00_u03b1_3950_: *mut LeanObject,
    mut v_ref_3951_: *mut LeanObject,
    mut v_msg_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3956_: *mut LeanObject = core::ptr::null_mut();
    v_res_3956_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(
        v_00_u03b1_3950_,
        v_ref_3951_,
        v_msg_3952_,
        v___y_3953_,
        v___y_3954_,
    );
    lean_dec(v___y_3954_);
    lean_dec_ref(v___y_3953_);
    lean_dec(v_ref_3951_);
    return v_res_3956_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(
    mut v_00_u03b1_3957_: *mut LeanObject,
    mut v_msg_3958_: *mut LeanObject,
    mut v___y_3959_: *mut LeanObject,
    mut v___y_3960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    v___x_3962_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_3958_, v___y_3959_, v___y_3960_);
    return v___x_3962_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(
    mut v_00_u03b1_3963_: *mut LeanObject,
    mut v_msg_3964_: *mut LeanObject,
    mut v___y_3965_: *mut LeanObject,
    mut v___y_3966_: *mut LeanObject,
    mut v___y_3967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3968_: *mut LeanObject = core::ptr::null_mut();
    v_res_3968_ =
        l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(
            v_00_u03b1_3963_,
            v_msg_3964_,
            v___y_3965_,
            v___y_3966_,
        );
    lean_dec(v___y_3966_);
    lean_dec_ref(v___y_3965_);
    return v_res_3968_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Elab_Expression(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Toml_Elab_Value(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_Toml_instInhabitedKeyTy_default = _init_l_Lake_Toml_instInhabitedKeyTy_default();
    l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy =
        _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Elab_Expression(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Toml_Grammar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Elab_Expression(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Toml_Elab_Value(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Toml_Grammar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Elab_Expression(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Elab_Expression(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Toml_Elab_Expression(builtin);
}

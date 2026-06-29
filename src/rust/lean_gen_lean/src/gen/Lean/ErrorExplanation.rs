// Lean compiler output
// Module: Lean.ErrorExplanation
// Imports: Lean.Message Lean.EnvExtension Lean.DocString.Links Lean.Message
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::DocString::Links::{
    initialize_Lean_DocString_Links, runtime_initialize_Lean_DocString_Links,
};
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg, runtime_initialize_Lean_EnvExtension,
};
use crate::r#gen::Lean::Message::{
    initialize_Lean_Message, l_Lean_MessageSeverity_toString,
    l_Lean_instFromJsonMessageSeverity_fromJson, l_Lean_instToJsonMessageSeverity_toJson,
    runtime_initialize_Lean_Message,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_foldl___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_dec_lt;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_array_to_list, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub, lean_usize_dec_eq,
};
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0_value:
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
    m_data: [115, 117, 109, 109, 97, 114, 121, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        69, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3_value:
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
    m_data: [77, 101, 116, 97, 100, 97, 116, 97, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18239673213070638308 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3_value)
            as *mut crate::leanh::LeanObject,
        16597581185784988388 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5777670751414481270 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [115, 105, 110, 99, 101, 86, 101, 114, 115, 105, 111, 110, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14_value:
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
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        8223184013717887766 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18_value:
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
    m_data: [115, 101, 118, 101, 114, 105, 116, 121, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19_value:
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
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18_value
        ) as *mut crate::leanh::LeanObject,
        2558814583289894876 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23_value:
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
        114, 101, 109, 111, 118, 101, 100, 86, 101, 114, 115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        114, 101, 109, 111, 118, 101, 100, 86, 101, 114, 115, 105, 111, 110, 63, 0,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25_value:
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
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24_value
        ) as *mut crate::leanh::LeanObject,
        13911480044048867773 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0_value:
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
    m_fun: l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_ErrorExplanation_instFromJsonMetadata: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0_value:
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
static mut l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_instToJsonMetadata___closed__0_value:
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
    m_fun: l_Lean_ErrorExplanation_instToJsonMetadata_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ErrorExplanation_instToJsonMetadata___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instToJsonMetadata___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_ErrorExplanation_instToJsonMetadata: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instToJsonMetadata___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_summaryWithSeverity___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l_Lean_ErrorExplanation_summaryWithSeverity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_summaryWithSeverity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ErrorExplanation_summaryWithSeverity___closed__1_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [41, 32, 0],
};
static mut l_Lean_ErrorExplanation_summaryWithSeverity___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_summaryWithSeverity___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 69, 120, 116, 0]};
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18446158502798500228 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_errorExplanationExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getErrorExplanations___redArg___lam__2___closed__0_value:
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
static mut l_Lean_getErrorExplanations___redArg___lam__2___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getErrorExplanations___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getErrorExplanations___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_getErrorExplanations___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getErrorExplanations___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getErrorExplanations___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getErrorExplanations___redArg___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_getErrorExplanations___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_getErrorExplanations___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getErrorExplanations___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(
    mut v_j_682_: *mut crate::leanh::LeanObject,
    mut v_k_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_684_ = l_Lean_Json_getObjValD(v_j_682_, v_k_683_);
    v___x_685_ = l_Lean_Json_getStr_x3f(v___x_684_);
    return v___x_685_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0___boxed(
    mut v_j_686_: *mut crate::leanh::LeanObject,
    mut v_k_687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_688_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(v_j_686_, v_k_687_);
    crate::leanh::lean_dec_ref(v_k_687_);
    return v_res_688_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(
    mut v_j_689_: *mut crate::leanh::LeanObject,
    mut v_k_690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = l_Lean_Json_getObjValD(v_j_689_, v_k_690_);
    v___x_692_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_691_);
    return v___x_692_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1___boxed(
    mut v_j_693_: *mut crate::leanh::LeanObject,
    mut v_k_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_695_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(v_j_693_, v_k_694_);
    crate::leanh::lean_dec_ref(v_k_694_);
    return v_res_695_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(
    mut v_x_698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v_a_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_698_) == 0 {
                    v___x_699_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0;
                    return v___x_699_;
                } else {
                    v___x_700_ = l_Lean_Json_getStr_x3f(v_x_698_);
                    if crate::leanh::lean_obj_tag(v___x_700_) == 0 {
                        v_a_701_ = crate::leanh::lean_ctor_get(v___x_700_, 0);
                        v_isSharedCheck_708_ = (!crate::leanh::lean_is_exclusive(v___x_700_)) as u8;
                        if v_isSharedCheck_708_ == 0 {
                            v___x_703_ = v___x_700_;
                            v_isShared_704_ = v_isSharedCheck_708_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_701_);
                            crate::leanh::lean_dec(v___x_700_);
                            v___x_703_ = crate::leanh::lean_box(0);
                            v_isShared_704_ = v_isSharedCheck_708_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_709_ = crate::leanh::lean_ctor_get(v___x_700_, 0);
                        v_isSharedCheck_717_ = (!crate::leanh::lean_is_exclusive(v___x_700_)) as u8;
                        if v_isSharedCheck_717_ == 0 {
                            v___x_711_ = v___x_700_;
                            v_isShared_712_ = v_isSharedCheck_717_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_709_);
                            crate::leanh::lean_dec(v___x_700_);
                            v___x_711_ = crate::leanh::lean_box(0);
                            v_isShared_712_ = v_isSharedCheck_717_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_704_ == 0 {
                    v___x_706_ = v___x_703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
                    v___x_706_ = v_reuseFailAlloc_707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_706_;
            }
            3 => {
                v___x_713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_713_, 0, v_a_709_);
                if v_isShared_712_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_711_, 0, v___x_713_);
                    v___x_715_ = v___x_711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_716_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
                    v___x_715_ = v_reuseFailAlloc_716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(
    mut v_j_718_: *mut crate::leanh::LeanObject,
    mut v_k_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_720_ = l_Lean_Json_getObjValD(v_j_718_, v_k_719_);
    v___x_721_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(v___x_720_);
    return v___x_721_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2___boxed(
    mut v_j_722_: *mut crate::leanh::LeanObject,
    mut v_k_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(v_j_722_, v_k_723_);
    crate::leanh::lean_dec_ref(v_k_723_);
    return v_res_724_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = 1;
    v___x_734_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4;
    v___x_735_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_734_, v___x_733_);
    return v___x_735_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6;
    v___x_738_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5,
    );
    v___x_739_ = lean_string_append(v___x_738_, v___x_737_);
    return v___x_739_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_742_: u8 = 0;
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_742_ = 1;
    v___x_743_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8;
    v___x_744_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_743_, v___x_742_);
    return v___x_744_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_745_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9,
    );
    v___x_746_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7,
    );
    v___x_747_ = lean_string_append(v___x_746_, v___x_745_);
    return v___x_747_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_749_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
    v___x_750_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10,
    );
    v___x_751_ = lean_string_append(v___x_750_, v___x_749_);
    return v___x_751_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_755_: u8 = 0;
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_755_ = 1;
    v___x_756_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14;
    v___x_757_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_756_, v___x_755_);
    return v___x_757_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15,
    );
    v___x_759_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7,
    );
    v___x_760_ = lean_string_append(v___x_759_, v___x_758_);
    return v___x_760_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
    v___x_762_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16,
    );
    v___x_763_ = lean_string_append(v___x_762_, v___x_761_);
    return v___x_763_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_767_: u8 = 0;
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_767_ = 1;
    v___x_768_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19;
    v___x_769_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_768_, v___x_767_);
    return v___x_769_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_770_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20,
    );
    v___x_771_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7,
    );
    v___x_772_ = lean_string_append(v___x_771_, v___x_770_);
    return v___x_772_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_773_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
    v___x_774_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21,
    );
    v___x_775_ = lean_string_append(v___x_774_, v___x_773_);
    return v___x_775_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_780_: u8 = 0;
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_780_ = 1;
    v___x_781_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25;
    v___x_782_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_781_, v___x_780_);
    return v___x_782_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_783_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26,
    );
    v___x_784_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7,
    );
    v___x_785_ = lean_string_append(v___x_784_, v___x_783_);
    return v___x_785_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_786_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
    v___x_787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27,
    );
    v___x_788_ = lean_string_append(v___x_787_, v___x_786_);
    return v___x_788_;
}
pub unsafe fn l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson(
    mut v_json_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_795_: u8 = 0;
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_801_: u8 = 0;
    let mut v_a_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_809_: u8 = 0;
    let mut v_a_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_816_: u8 = 0;
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_822_: u8 = 0;
    let mut v_a_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_830_: u8 = 0;
    let mut v_a_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_837_: u8 = 0;
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_843_: u8 = 0;
    let mut v_a_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_851_: u8 = 0;
    let mut v_a_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_864_: u8 = 0;
    let mut v_a_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut v_a_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_790_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0;
                crate::leanh::lean_inc(v_json_789_);
                v___x_791_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(v_json_789_, v___x_790_);
                if crate::leanh::lean_obj_tag(v___x_791_) == 0 {
                    crate::leanh::lean_dec(v_json_789_);
                    v_a_792_ = crate::leanh::lean_ctor_get(v___x_791_, 0);
                    v_isSharedCheck_801_ = (!crate::leanh::lean_is_exclusive(v___x_791_)) as u8;
                    if v_isSharedCheck_801_ == 0 {
                        v___x_794_ = v___x_791_;
                        v_isShared_795_ = v_isSharedCheck_801_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_792_);
                        crate::leanh::lean_dec(v___x_791_);
                        v___x_794_ = crate::leanh::lean_box(0);
                        v_isShared_795_ = v_isSharedCheck_801_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_791_) == 0 {
                        crate::leanh::lean_dec(v_json_789_);
                        v_a_802_ = crate::leanh::lean_ctor_get(v___x_791_, 0);
                        v_isSharedCheck_809_ = (!crate::leanh::lean_is_exclusive(v___x_791_)) as u8;
                        if v_isSharedCheck_809_ == 0 {
                            v___x_804_ = v___x_791_;
                            v_isShared_805_ = v_isSharedCheck_809_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_802_);
                            crate::leanh::lean_dec(v___x_791_);
                            v___x_804_ = crate::leanh::lean_box(0);
                            v_isShared_805_ = v_isSharedCheck_809_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_810_ = crate::leanh::lean_ctor_get(v___x_791_, 0);
                        crate::leanh::lean_inc(v_a_810_);
                        crate::leanh::lean_dec_ref_known(v___x_791_, 1);
                        v___x_811_ =
                            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13;
                        crate::leanh::lean_inc(v_json_789_);
                        v___x_812_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(v_json_789_, v___x_811_);
                        if crate::leanh::lean_obj_tag(v___x_812_) == 0 {
                            crate::leanh::lean_dec(v_a_810_);
                            crate::leanh::lean_dec(v_json_789_);
                            v_a_813_ = crate::leanh::lean_ctor_get(v___x_812_, 0);
                            v_isSharedCheck_822_ =
                                (!crate::leanh::lean_is_exclusive(v___x_812_)) as u8;
                            if v_isSharedCheck_822_ == 0 {
                                v___x_815_ = v___x_812_;
                                v_isShared_816_ = v_isSharedCheck_822_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_813_);
                                crate::leanh::lean_dec(v___x_812_);
                                v___x_815_ = crate::leanh::lean_box(0);
                                v_isShared_816_ = v_isSharedCheck_822_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_812_) == 0 {
                                crate::leanh::lean_dec(v_a_810_);
                                crate::leanh::lean_dec(v_json_789_);
                                v_a_823_ = crate::leanh::lean_ctor_get(v___x_812_, 0);
                                v_isSharedCheck_830_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_812_)) as u8;
                                if v_isSharedCheck_830_ == 0 {
                                    v___x_825_ = v___x_812_;
                                    v_isShared_826_ = v_isSharedCheck_830_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_823_);
                                    crate::leanh::lean_dec(v___x_812_);
                                    v___x_825_ = crate::leanh::lean_box(0);
                                    v_isShared_826_ = v_isSharedCheck_830_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_831_ = crate::leanh::lean_ctor_get(v___x_812_, 0);
                                crate::leanh::lean_inc(v_a_831_);
                                crate::leanh::lean_dec_ref_known(v___x_812_, 1);
                                v___x_832_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18;
                                crate::leanh::lean_inc(v_json_789_);
                                v___x_833_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(v_json_789_, v___x_832_);
                                if crate::leanh::lean_obj_tag(v___x_833_) == 0 {
                                    crate::leanh::lean_dec(v_a_831_);
                                    crate::leanh::lean_dec(v_a_810_);
                                    crate::leanh::lean_dec(v_json_789_);
                                    v_a_834_ = crate::leanh::lean_ctor_get(v___x_833_, 0);
                                    v_isSharedCheck_843_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_833_)) as u8;
                                    if v_isSharedCheck_843_ == 0 {
                                        v___x_836_ = v___x_833_;
                                        v_isShared_837_ = v_isSharedCheck_843_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_834_);
                                        crate::leanh::lean_dec(v___x_833_);
                                        v___x_836_ = crate::leanh::lean_box(0);
                                        v_isShared_837_ = v_isSharedCheck_843_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_833_) == 0 {
                                        crate::leanh::lean_dec(v_a_831_);
                                        crate::leanh::lean_dec(v_a_810_);
                                        crate::leanh::lean_dec(v_json_789_);
                                        v_a_844_ = crate::leanh::lean_ctor_get(v___x_833_, 0);
                                        v_isSharedCheck_851_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_833_)) as u8;
                                        if v_isSharedCheck_851_ == 0 {
                                            v___x_846_ = v___x_833_;
                                            v_isShared_847_ = v_isSharedCheck_851_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_844_);
                                            crate::leanh::lean_dec(v___x_833_);
                                            v___x_846_ = crate::leanh::lean_box(0);
                                            v_isShared_847_ = v_isSharedCheck_851_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_852_ = crate::leanh::lean_ctor_get(v___x_833_, 0);
                                        crate::leanh::lean_inc(v_a_852_);
                                        crate::leanh::lean_dec_ref_known(v___x_833_, 1);
                                        v___x_853_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23;
                                        v___x_854_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(v_json_789_, v___x_853_);
                                        if crate::leanh::lean_obj_tag(v___x_854_) == 0 {
                                            crate::leanh::lean_dec(v_a_852_);
                                            crate::leanh::lean_dec(v_a_831_);
                                            crate::leanh::lean_dec(v_a_810_);
                                            v_a_855_ = crate::leanh::lean_ctor_get(v___x_854_, 0);
                                            v_isSharedCheck_864_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_854_))
                                                    as u8;
                                            if v_isSharedCheck_864_ == 0 {
                                                v___x_857_ = v___x_854_;
                                                v_isShared_858_ = v_isSharedCheck_864_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_855_);
                                                crate::leanh::lean_dec(v___x_854_);
                                                v___x_857_ = crate::leanh::lean_box(0);
                                                v_isShared_858_ = v_isSharedCheck_864_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if crate::leanh::lean_obj_tag(v___x_854_) == 0 {
                                                crate::leanh::lean_dec(v_a_852_);
                                                crate::leanh::lean_dec(v_a_831_);
                                                crate::leanh::lean_dec(v_a_810_);
                                                v_a_865_ =
                                                    crate::leanh::lean_ctor_get(v___x_854_, 0);
                                                v_isSharedCheck_872_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_854_))
                                                        as u8;
                                                if v_isSharedCheck_872_ == 0 {
                                                    v___x_867_ = v___x_854_;
                                                    v_isShared_868_ = v_isSharedCheck_872_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_865_);
                                                    crate::leanh::lean_dec(v___x_854_);
                                                    v___x_867_ = crate::leanh::lean_box(0);
                                                    v_isShared_868_ = v_isSharedCheck_872_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_873_ =
                                                    crate::leanh::lean_ctor_get(v___x_854_, 0);
                                                v_isSharedCheck_882_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_854_))
                                                        as u8;
                                                if v_isSharedCheck_882_ == 0 {
                                                    v___x_875_ = v___x_854_;
                                                    v_isShared_876_ = v_isSharedCheck_882_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_873_);
                                                    crate::leanh::lean_dec(v___x_854_);
                                                    v___x_875_ = crate::leanh::lean_box(0);
                                                    v_isShared_876_ = v_isSharedCheck_882_;
                                                    state = 17;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_796_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12_once
                    ),
                    _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12,
                );
                v___x_797_ = lean_string_append(v___x_796_, v_a_792_);
                crate::leanh::lean_dec(v_a_792_);
                if v_isShared_795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_794_, 0, v___x_797_);
                    v___x_799_ = v___x_794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_800_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
                    v___x_799_ = v_reuseFailAlloc_800_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_799_;
            }
            3 => {
                if v_isShared_805_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_804_, 0);
                    v___x_807_ = v___x_804_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_808_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
                    v___x_807_ = v_reuseFailAlloc_808_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_807_;
            }
            5 => {
                v___x_817_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17_once
                    ),
                    _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17,
                );
                v___x_818_ = lean_string_append(v___x_817_, v_a_813_);
                crate::leanh::lean_dec(v_a_813_);
                if v_isShared_816_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_815_, 0, v___x_818_);
                    v___x_820_ = v___x_815_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_821_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
                    v___x_820_ = v_reuseFailAlloc_821_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_820_;
            }
            7 => {
                if v_isShared_826_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_825_, 0);
                    v___x_828_ = v___x_825_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
                    v___x_828_ = v_reuseFailAlloc_829_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_828_;
            }
            9 => {
                v___x_838_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22_once
                    ),
                    _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22,
                );
                v___x_839_ = lean_string_append(v___x_838_, v_a_834_);
                crate::leanh::lean_dec(v_a_834_);
                if v_isShared_837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_836_, 0, v___x_839_);
                    v___x_841_ = v___x_836_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_842_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
                    v___x_841_ = v_reuseFailAlloc_842_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_841_;
            }
            11 => {
                if v_isShared_847_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_846_, 0);
                    v___x_849_ = v___x_846_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_850_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
                    v___x_849_ = v_reuseFailAlloc_850_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_849_;
            }
            13 => {
                v___x_859_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28_once
                    ),
                    _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28,
                );
                v___x_860_ = lean_string_append(v___x_859_, v_a_855_);
                crate::leanh::lean_dec(v_a_855_);
                if v_isShared_858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_857_, 0, v___x_860_);
                    v___x_862_ = v___x_857_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
                    v___x_862_ = v_reuseFailAlloc_863_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_862_;
            }
            15 => {
                if v_isShared_868_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_867_, 0);
                    v___x_870_ = v___x_867_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_871_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
                    v___x_870_ = v_reuseFailAlloc_871_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_870_;
            }
            17 => {
                v___x_877_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_877_, 0, v_a_810_);
                crate::leanh::lean_ctor_set(v___x_877_, 1, v_a_831_);
                crate::leanh::lean_ctor_set(v___x_877_, 2, v_a_873_);
                v___x_878_ = (crate::leanh::lean_unbox(v_a_852_) as u8);
                crate::leanh::lean_dec(v_a_852_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_877_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_878_,
                );
                if v_isShared_876_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_875_, 0, v___x_877_);
                    v___x_880_ = v___x_875_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_877_);
                    v___x_880_ = v_reuseFailAlloc_881_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(
    mut v_k_885_: *mut crate::leanh::LeanObject,
    mut v_x_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_886_) == 0 {
                    crate::leanh::lean_dec_ref(v_k_885_);
                    v___x_887_ = crate::leanh::lean_box(0);
                    return v___x_887_;
                } else {
                    v_val_888_ = crate::leanh::lean_ctor_get(v_x_886_, 0);
                    v_isSharedCheck_898_ = (!crate::leanh::lean_is_exclusive(v_x_886_)) as u8;
                    if v_isSharedCheck_898_ == 0 {
                        v___x_890_ = v_x_886_;
                        v_isShared_891_ = v_isSharedCheck_898_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_888_);
                        crate::leanh::lean_dec(v_x_886_);
                        v___x_890_ = crate::leanh::lean_box(0);
                        v_isShared_891_ = v_isSharedCheck_898_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_891_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_890_, 3);
                    v___x_893_ = v___x_890_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_897_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_897_, 0, v_val_888_);
                    v___x_893_ = v_reuseFailAlloc_897_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_894_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_894_, 0, v_k_885_);
                crate::leanh::lean_ctor_set(v___x_894_, 1, v___x_893_);
                v___x_895_ = crate::leanh::lean_box(0);
                v___x_896_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_894_);
                crate::leanh::lean_ctor_set(v___x_896_, 1, v___x_895_);
                return v___x_896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(
    mut v_a_899_: *mut crate::leanh::LeanObject,
    mut v_a_900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_899_) == 0 {
                    v___x_901_ = lean_array_to_list(v_a_900_);
                    return v___x_901_;
                } else {
                    v_head_902_ = crate::leanh::lean_ctor_get(v_a_899_, 0);
                    crate::leanh::lean_inc(v_head_902_);
                    v_tail_903_ = crate::leanh::lean_ctor_get(v_a_899_, 1);
                    crate::leanh::lean_inc(v_tail_903_);
                    crate::leanh::lean_dec_ref_known(v_a_899_, 2);
                    v___x_904_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_900_,
                        v_head_902_,
                    );
                    v_a_899_ = v_tail_903_;
                    v_a_900_ = v___x_904_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ErrorExplanation_instToJsonMetadata_toJson(
    mut v_x_908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_summary_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sinceVersion_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_911_: u8 = 0;
    let mut v_removedVersion_x3f_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_summary_909_ = crate::leanh::lean_ctor_get(v_x_908_, 0);
    crate::leanh::lean_inc_ref(v_summary_909_);
    v_sinceVersion_910_ = crate::leanh::lean_ctor_get(v_x_908_, 1);
    crate::leanh::lean_inc_ref(v_sinceVersion_910_);
    v_severity_911_ = crate::leanh::lean_ctor_get_uint8(
        v_x_908_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v_removedVersion_x3f_912_ = crate::leanh::lean_ctor_get(v_x_908_, 2);
    crate::leanh::lean_inc(v_removedVersion_x3f_912_);
    crate::leanh::lean_dec_ref(v_x_908_);
    v___x_913_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0;
    v___x_914_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_914_, 0, v_summary_909_);
    v___x_915_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_915_, 0, v___x_913_);
    crate::leanh::lean_ctor_set(v___x_915_, 1, v___x_914_);
    v___x_916_ = crate::leanh::lean_box(0);
    v___x_917_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_917_, 0, v___x_915_);
    crate::leanh::lean_ctor_set(v___x_917_, 1, v___x_916_);
    v___x_918_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13;
    v___x_919_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_919_, 0, v_sinceVersion_910_);
    v___x_920_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_920_, 0, v___x_918_);
    crate::leanh::lean_ctor_set(v___x_920_, 1, v___x_919_);
    v___x_921_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_921_, 0, v___x_920_);
    crate::leanh::lean_ctor_set(v___x_921_, 1, v___x_916_);
    v___x_922_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18;
    v___x_923_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_911_);
    v___x_924_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_924_, 0, v___x_922_);
    crate::leanh::lean_ctor_set(v___x_924_, 1, v___x_923_);
    v___x_925_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_925_, 0, v___x_924_);
    crate::leanh::lean_ctor_set(v___x_925_, 1, v___x_916_);
    v___x_926_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23;
    v___x_927_ = l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(
        v___x_926_,
        v_removedVersion_x3f_912_,
    );
    v___x_928_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_928_, 0, v___x_927_);
    crate::leanh::lean_ctor_set(v___x_928_, 1, v___x_916_);
    v___x_929_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_929_, 0, v___x_925_);
    crate::leanh::lean_ctor_set(v___x_929_, 1, v___x_928_);
    v___x_930_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_930_, 0, v___x_921_);
    crate::leanh::lean_ctor_set(v___x_930_, 1, v___x_929_);
    v___x_931_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_931_, 0, v___x_917_);
    crate::leanh::lean_ctor_set(v___x_931_, 1, v___x_930_);
    v___x_932_ = l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0;
    v___x_933_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(v___x_931_, v___x_932_);
    v___x_934_ = l_Lean_Json_mkObj(v___x_933_);
    crate::leanh::lean_dec(v___x_933_);
    return v___x_934_;
}
pub unsafe fn l_Lean_ErrorExplanation_summaryWithSeverity(
    mut v_explan_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_metadata_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_summary_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_942_: u8 = 0;
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_metadata_940_ = crate::leanh::lean_ctor_get(v_explan_939_, 1);
    v_summary_941_ = crate::leanh::lean_ctor_get(v_metadata_940_, 0);
    v_severity_942_ = crate::leanh::lean_ctor_get_uint8(
        v_metadata_940_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v___x_943_ = l_Lean_ErrorExplanation_summaryWithSeverity___closed__0;
    v___x_944_ = l_Lean_MessageSeverity_toString(v_severity_942_);
    v___x_945_ = lean_string_append(v___x_943_, v___x_944_);
    crate::leanh::lean_dec_ref(v___x_944_);
    v___x_946_ = l_Lean_ErrorExplanation_summaryWithSeverity___closed__1;
    v___x_947_ = lean_string_append(v___x_945_, v___x_946_);
    v___x_948_ = lean_string_append(v___x_947_, v_summary_941_);
    return v___x_948_;
}
pub unsafe fn l_Lean_ErrorExplanation_summaryWithSeverity___boxed(
    mut v_explan_949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_950_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_explan_949_);
    crate::leanh::lean_dec_ref(v_explan_949_);
    return v_res_950_;
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(
    mut v_s_951_: *mut crate::leanh::LeanObject,
    mut v_x_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_953_ = crate::leanh::lean_ctor_get(v_x_952_, 0);
    crate::leanh::lean_inc(v_fst_953_);
    v_snd_954_ = crate::leanh::lean_ctor_get(v_x_952_, 1);
    crate::leanh::lean_inc(v_snd_954_);
    crate::leanh::lean_dec_ref(v_x_952_);
    v___x_955_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_fst_953_, v_snd_954_, v_s_951_,
    );
    return v___x_955_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_956_: *mut crate::leanh::LeanObject,
    mut v_i_957_: usize,
    mut v_stop_958_: usize,
    mut v_b_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_960_: u8 = 0;
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: usize = 0;
    let mut v___x_966_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_960_ = lean_usize_dec_eq(v_i_957_, v_stop_958_);
                if v___x_960_ == 0 {
                    v___x_961_ = lean_array_uget_borrowed(v_as_956_, v_i_957_);
                    v_fst_962_ = crate::leanh::lean_ctor_get(v___x_961_, 0);
                    v_snd_963_ = crate::leanh::lean_ctor_get(v___x_961_, 1);
                    crate::leanh::lean_inc(v_snd_963_);
                    crate::leanh::lean_inc(v_fst_962_);
                    v___x_964_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_962_, v_snd_963_, v_b_959_);
                    v___x_965_ = 1usize;
                    v___x_966_ = lean_usize_add(v_i_957_, v___x_965_);
                    v_i_957_ = v___x_966_;
                    v_b_959_ = v___x_964_;
                    state = 0;
                    continue;
                } else {
                    return v_b_959_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_as_968_: *mut crate::leanh::LeanObject,
    mut v_i_969_: *mut crate::leanh::LeanObject,
    mut v_stop_970_: *mut crate::leanh::LeanObject,
    mut v_b_971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_972_: usize = 0;
    let mut v_stop_boxed_973_: usize = 0;
    let mut v_res_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_972_ = crate::leanh::lean_unbox_usize(v_i_969_);
    crate::leanh::lean_dec(v_i_969_);
    v_stop_boxed_973_ = crate::leanh::lean_unbox_usize(v_stop_970_);
    crate::leanh::lean_dec(v_stop_970_);
    v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(v_as_968_, v_i_boxed_972_, v_stop_boxed_973_, v_b_971_);
    crate::leanh::lean_dec_ref(v_as_968_);
    return v_res_974_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(
    mut v_as_975_: *mut crate::leanh::LeanObject,
    mut v_i_976_: usize,
    mut v_stop_977_: usize,
    mut v_b_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_979_: u8 = 0;
    v___x_979_ = lean_usize_dec_eq(v_i_976_, v_stop_977_);
    if v___x_979_ == 0 {
        let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: usize = 0;
        let mut v___x_985_: usize = 0;
        let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_980_ = lean_array_uget_borrowed(v_as_975_, v_i_976_);
        v_fst_981_ = crate::leanh::lean_ctor_get(v___x_980_, 0);
        v_snd_982_ = crate::leanh::lean_ctor_get(v___x_980_, 1);
        crate::leanh::lean_inc(v_snd_982_);
        crate::leanh::lean_inc(v_fst_981_);
        v___x_983_ =
            l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
                v_fst_981_, v_snd_982_, v_b_978_,
            );
        v___x_984_ = 1usize;
        v___x_985_ = lean_usize_add(v_i_976_, v___x_984_);
        v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(v_as_975_, v___x_985_, v_stop_977_, v___x_983_);
        return v___x_986_;
    } else {
        return v_b_978_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0___boxed(
    mut v_as_987_: *mut crate::leanh::LeanObject,
    mut v_i_988_: *mut crate::leanh::LeanObject,
    mut v_stop_989_: *mut crate::leanh::LeanObject,
    mut v_b_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_991_: usize = 0;
    let mut v_stop_boxed_992_: usize = 0;
    let mut v_res_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_991_ = crate::leanh::lean_unbox_usize(v_i_988_);
    crate::leanh::lean_dec(v_i_988_);
    v_stop_boxed_992_ = crate::leanh::lean_unbox_usize(v_stop_989_);
    crate::leanh::lean_dec(v_stop_989_);
    v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v_as_987_, v_i_boxed_991_, v_stop_boxed_992_, v_b_990_);
    crate::leanh::lean_dec_ref(v_as_987_);
    return v_res_993_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(
    mut v_as_994_: *mut crate::leanh::LeanObject,
    mut v_i_995_: usize,
    mut v_stop_996_: usize,
    mut v_b_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: usize = 0;
    let mut v___x_1001_: usize = 0;
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: u8 = 0;
    let mut v___x_1008_: u8 = 0;
    let mut v___x_1009_: usize = 0;
    let mut v___x_1010_: usize = 0;
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: usize = 0;
    let mut v___x_1013_: usize = 0;
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1003_ = lean_usize_dec_eq(v_i_995_, v_stop_996_);
                if v___x_1003_ == 0 {
                    v___x_1004_ = lean_array_uget_borrowed(v_as_994_, v_i_995_);
                    v___x_1005_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1006_ = lean_array_get_size(v___x_1004_);
                    v___x_1007_ = lean_nat_dec_lt(v___x_1005_, v___x_1006_);
                    if v___x_1007_ == 0 {
                        v___y_999_ = v_b_997_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1008_ = lean_nat_dec_le(v___x_1006_, v___x_1006_);
                        if v___x_1008_ == 0 {
                            if v___x_1007_ == 0 {
                                v___y_999_ = v_b_997_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1009_ = 0usize;
                                v___x_1010_ = lean_usize_of_nat(v___x_1006_);
                                v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v___x_1004_, v___x_1009_, v___x_1010_, v_b_997_);
                                v___y_999_ = v___x_1011_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1012_ = 0usize;
                            v___x_1013_ = lean_usize_of_nat(v___x_1006_);
                            v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v___x_1004_, v___x_1012_, v___x_1013_, v_b_997_);
                            v___y_999_ = v___x_1014_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_997_;
                }
            }
            1 => {
                v___x_1000_ = 1usize;
                v___x_1001_ = lean_usize_add(v_i_995_, v___x_1000_);
                v_i_995_ = v___x_1001_;
                v_b_997_ = v___y_999_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1___boxed(
    mut v_as_1015_: *mut crate::leanh::LeanObject,
    mut v_i_1016_: *mut crate::leanh::LeanObject,
    mut v_stop_1017_: *mut crate::leanh::LeanObject,
    mut v_b_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1019_: usize = 0;
    let mut v_stop_boxed_1020_: usize = 0;
    let mut v_res_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1019_ = crate::leanh::lean_unbox_usize(v_i_1016_);
    crate::leanh::lean_dec(v_i_1016_);
    v_stop_boxed_1020_ = crate::leanh::lean_unbox_usize(v_stop_1017_);
    crate::leanh::lean_dec(v_stop_1017_);
    v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_as_1015_, v_i_boxed_1019_, v_stop_boxed_1020_, v_b_1018_);
    crate::leanh::lean_dec_ref(v_as_1015_);
    return v_res_1021_;
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(
    mut v_ess_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    v___x_1023_ = crate::leanh::lean_box(1);
    v___x_1024_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1025_ = lean_array_get_size(v_ess_1022_);
    v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
    if v___x_1026_ == 0 {
        return v___x_1023_;
    } else {
        let mut v___x_1027_: u8 = 0;
        v___x_1027_ = lean_nat_dec_le(v___x_1025_, v___x_1025_);
        if v___x_1027_ == 0 {
            if v___x_1026_ == 0 {
                return v___x_1023_;
            } else {
                let mut v___x_1028_: usize = 0;
                let mut v___x_1029_: usize = 0;
                let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1028_ = 0usize;
                v___x_1029_ = lean_usize_of_nat(v___x_1025_);
                v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_ess_1022_, v___x_1028_, v___x_1029_, v___x_1023_);
                return v___x_1030_;
            }
        } else {
            let mut v___x_1031_: usize = 0;
            let mut v___x_1032_: usize = 0;
            let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1031_ = 0usize;
            v___x_1032_ = lean_usize_of_nat(v___x_1025_);
            v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_ess_1022_, v___x_1031_, v___x_1032_, v___x_1023_);
            return v___x_1033_;
        }
    }
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(
    mut v_ess_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1035_ = l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(v_ess_1034_);
    crate::leanh::lean_dec_ref(v_ess_1034_);
    return v_res_1035_;
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(
    mut v_es_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = lean_array_mk(v_es_1036_);
    return v___x_1037_;
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1053_ = l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
    v___x_1054_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(
    mut v_a_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
    return v_res_1056_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___redArg___lam__0(
    mut v___x_1057_: *mut crate::leanh::LeanObject,
    mut v_name_1058_: *mut crate::leanh::LeanObject,
    mut v_toPure_1059_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1061_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_1062_ = crate::leanh::lean_ctor_get(v___x_1061_, 0);
    v_asyncMode_1063_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1062_, 2);
    v___x_1064_ = crate::leanh::lean_box(0);
    v___x_1065_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1057_,
        v___x_1061_,
        v_____do__lift_1060_,
        v_asyncMode_1063_,
        v___x_1064_,
    );
    v___x_1066_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_1065_,
            v_name_1058_,
        );
    crate::leanh::lean_dec(v___x_1065_);
    v___x_1067_ =
        crate::leanh::lean_apply_2(v_toPure_1059_, crate::leanh::lean_box(0), v___x_1066_);
    return v___x_1067_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed(
    mut v___x_1068_: *mut crate::leanh::LeanObject,
    mut v_name_1069_: *mut crate::leanh::LeanObject,
    mut v_toPure_1070_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1072_ = l_Lean_getErrorExplanation_x3f___redArg___lam__0(
        v___x_1068_,
        v_name_1069_,
        v_toPure_1070_,
        v_____do__lift_1071_,
    );
    crate::leanh::lean_dec(v_name_1069_);
    return v_res_1072_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___redArg(
    mut v_inst_1073_: *mut crate::leanh::LeanObject,
    mut v_inst_1074_: *mut crate::leanh::LeanObject,
    mut v_name_1075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1076_ = crate::leanh::lean_ctor_get(v_inst_1073_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1076_);
    v_toBind_1077_ = crate::leanh::lean_ctor_get(v_inst_1073_, 1);
    crate::leanh::lean_inc(v_toBind_1077_);
    crate::leanh::lean_dec_ref(v_inst_1073_);
    v_getEnv_1078_ = crate::leanh::lean_ctor_get(v_inst_1074_, 0);
    crate::leanh::lean_inc(v_getEnv_1078_);
    crate::leanh::lean_dec_ref(v_inst_1074_);
    v_toPure_1079_ = crate::leanh::lean_ctor_get(v_toApplicative_1076_, 1);
    crate::leanh::lean_inc(v_toPure_1079_);
    crate::leanh::lean_dec_ref(v_toApplicative_1076_);
    v___x_1080_ = crate::leanh::lean_box(1);
    v___f_1081_ = crate::leanh::lean_alloc_closure(
        l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1081_, 0, v___x_1080_);
    crate::leanh::lean_closure_set(v___f_1081_, 1, v_name_1075_);
    crate::leanh::lean_closure_set(v___f_1081_, 2, v_toPure_1079_);
    v___x_1082_ = crate::leanh::lean_apply_4(
        v_toBind_1077_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1078_,
        v___f_1081_,
    );
    return v___x_1082_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f(
    mut v_m_1083_: *mut crate::leanh::LeanObject,
    mut v_inst_1084_: *mut crate::leanh::LeanObject,
    mut v_inst_1085_: *mut crate::leanh::LeanObject,
    mut v_name_1086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = l_Lean_getErrorExplanation_x3f___redArg(v_inst_1084_, v_inst_1085_, v_name_1086_);
    return v___x_1087_;
}
pub unsafe fn l_Lean_getErrorExplanationRaw_x3f(
    mut v_env_1088_: *mut crate::leanh::LeanObject,
    mut v_name_1089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1090_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_1091_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
    v_asyncMode_1092_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1091_, 2);
    v___x_1093_ = crate::leanh::lean_box(1);
    v___x_1094_ = crate::leanh::lean_box(0);
    v___x_1095_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1093_,
        v___x_1090_,
        v_env_1088_,
        v_asyncMode_1092_,
        v___x_1094_,
    );
    v___x_1096_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_1095_,
            v_name_1089_,
        );
    crate::leanh::lean_dec(v___x_1095_);
    return v___x_1096_;
}
pub unsafe fn l_Lean_getErrorExplanationRaw_x3f___boxed(
    mut v_env_1097_: *mut crate::leanh::LeanObject,
    mut v_name_1098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1099_ = l_Lean_getErrorExplanationRaw_x3f(v_env_1097_, v_name_1098_);
    crate::leanh::lean_dec(v_name_1098_);
    return v_res_1099_;
}
pub unsafe fn l_Lean_hasErrorExplanation___redArg___lam__0(
    mut v___x_1100_: *mut crate::leanh::LeanObject,
    mut v_name_1101_: *mut crate::leanh::LeanObject,
    mut v_toPure_1102_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u8 = 0;
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_1105_ = crate::leanh::lean_ctor_get(v___x_1104_, 0);
    v_asyncMode_1106_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1105_, 2);
    v___x_1107_ = crate::leanh::lean_box(0);
    v___x_1108_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1100_,
        v___x_1104_,
        v_____do__lift_1103_,
        v_asyncMode_1106_,
        v___x_1107_,
    );
    v___x_1109_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_name_1101_,
            v___x_1108_,
        );
    crate::leanh::lean_dec(v___x_1108_);
    v___x_1110_ = crate::leanh::lean_box((v___x_1109_) as usize);
    v___x_1111_ =
        crate::leanh::lean_apply_2(v_toPure_1102_, crate::leanh::lean_box(0), v___x_1110_);
    return v___x_1111_;
}
pub unsafe fn l_Lean_hasErrorExplanation___redArg___lam__0___boxed(
    mut v___x_1112_: *mut crate::leanh::LeanObject,
    mut v_name_1113_: *mut crate::leanh::LeanObject,
    mut v_toPure_1114_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Lean_hasErrorExplanation___redArg___lam__0(
        v___x_1112_,
        v_name_1113_,
        v_toPure_1114_,
        v_____do__lift_1115_,
    );
    crate::leanh::lean_dec(v_name_1113_);
    return v_res_1116_;
}
pub unsafe fn l_Lean_hasErrorExplanation___redArg(
    mut v_inst_1117_: *mut crate::leanh::LeanObject,
    mut v_inst_1118_: *mut crate::leanh::LeanObject,
    mut v_name_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1120_ = crate::leanh::lean_ctor_get(v_inst_1117_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1120_);
    v_toBind_1121_ = crate::leanh::lean_ctor_get(v_inst_1117_, 1);
    crate::leanh::lean_inc(v_toBind_1121_);
    crate::leanh::lean_dec_ref(v_inst_1117_);
    v_getEnv_1122_ = crate::leanh::lean_ctor_get(v_inst_1118_, 0);
    crate::leanh::lean_inc(v_getEnv_1122_);
    crate::leanh::lean_dec_ref(v_inst_1118_);
    v_toPure_1123_ = crate::leanh::lean_ctor_get(v_toApplicative_1120_, 1);
    crate::leanh::lean_inc(v_toPure_1123_);
    crate::leanh::lean_dec_ref(v_toApplicative_1120_);
    v___x_1124_ = crate::leanh::lean_box(1);
    v___f_1125_ = crate::leanh::lean_alloc_closure(
        l_Lean_hasErrorExplanation___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1125_, 0, v___x_1124_);
    crate::leanh::lean_closure_set(v___f_1125_, 1, v_name_1119_);
    crate::leanh::lean_closure_set(v___f_1125_, 2, v_toPure_1123_);
    v___x_1126_ = crate::leanh::lean_apply_4(
        v_toBind_1121_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1122_,
        v___f_1125_,
    );
    return v___x_1126_;
}
pub unsafe fn l_Lean_hasErrorExplanation(
    mut v_m_1127_: *mut crate::leanh::LeanObject,
    mut v_inst_1128_: *mut crate::leanh::LeanObject,
    mut v_inst_1129_: *mut crate::leanh::LeanObject,
    mut v_name_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = l_Lean_hasErrorExplanation___redArg(v_inst_1128_, v_inst_1129_, v_name_1130_);
    return v___x_1131_;
}
pub unsafe fn l_Lean_getErrorExplanations___redArg___lam__0(
    mut v_e_1132_: *mut crate::leanh::LeanObject,
    mut v_e_x27_1133_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: u8 = 0;
    v_fst_1134_ = crate::leanh::lean_ctor_get(v_e_1132_, 0);
    crate::leanh::lean_inc(v_fst_1134_);
    crate::leanh::lean_dec_ref(v_e_1132_);
    v_fst_1135_ = crate::leanh::lean_ctor_get(v_e_x27_1133_, 0);
    crate::leanh::lean_inc(v_fst_1135_);
    crate::leanh::lean_dec_ref(v_e_x27_1133_);
    v___x_1136_ = 1;
    v___x_1137_ = l_Lean_Name_toString(v_fst_1134_, v___x_1136_);
    v___x_1138_ = l_Lean_Name_toString(v_fst_1135_, v___x_1136_);
    v___x_1139_ = lean_string_dec_lt(v___x_1137_, v___x_1138_);
    crate::leanh::lean_dec_ref(v___x_1138_);
    crate::leanh::lean_dec_ref(v___x_1137_);
    return v___x_1139_;
}
pub unsafe fn l_Lean_getErrorExplanations___redArg___lam__0___boxed(
    mut v_e_1140_: *mut crate::leanh::LeanObject,
    mut v_e_x27_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1142_: u8 = 0;
    let mut v_r_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_Lean_getErrorExplanations___redArg___lam__0(v_e_1140_, v_e_x27_1141_);
    v_r_1143_ = crate::leanh::lean_box((v_res_1142_) as usize);
    return v_r_1143_;
}
pub unsafe fn l_Lean_getErrorExplanations___redArg___lam__1(
    mut v_acc_1144_: *mut crate::leanh::LeanObject,
    mut v_k_1145_: *mut crate::leanh::LeanObject,
    mut v_v_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1147_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1147_, 0, v_k_1145_);
    crate::leanh::lean_ctor_set(v___x_1147_, 1, v_v_1146_);
    v___x_1148_ = lean_array_push(v_acc_1144_, v___x_1147_);
    return v___x_1148_;
}
pub unsafe fn l_Lean_getErrorExplanations___redArg___lam__2(
    mut v___x_1151_: *mut crate::leanh::LeanObject,
    mut v___f_1152_: *mut crate::leanh::LeanObject,
    mut v___f_1153_: *mut crate::leanh::LeanObject,
    mut v_toPure_1154_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: u8 = 0;
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1156_ = l_Lean_errorExplanationExt;
                v_toEnvExtension_1157_ = crate::leanh::lean_ctor_get(v___x_1156_, 0);
                v_asyncMode_1158_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1157_, 2);
                v___x_1159_ = crate::leanh::lean_box(0);
                v___x_1160_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_1151_,
                    v___x_1156_,
                    v_____do__lift_1155_,
                    v_asyncMode_1158_,
                    v___x_1159_,
                );
                v___x_1161_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1162_ = l_Lean_getErrorExplanations___redArg___lam__2___closed__0;
                v___x_1163_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_1152_,
                    v___x_1162_,
                    v___x_1160_,
                );
                v___x_1164_ = lean_array_get_size(v___x_1163_);
                v___x_1170_ = lean_nat_dec_eq(v___x_1164_, v___x_1161_);
                if v___x_1170_ == 0 {
                    v___x_1171_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1172_ = lean_nat_sub(v___x_1164_, v___x_1171_);
                    v___x_1176_ = lean_nat_dec_le(v___x_1161_, v___x_1172_);
                    if v___x_1176_ == 0 {
                        crate::leanh::lean_inc(v___x_1172_);
                        v___y_1174_ = v___x_1172_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1174_ = v___x_1161_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_1153_);
                    v___x_1177_ = crate::leanh::lean_apply_2(
                        v_toPure_1154_,
                        crate::leanh::lean_box(0),
                        v___x_1163_,
                    );
                    return v___x_1177_;
                }
            }
            1 => {
                v___x_1168_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    crate::leanh::lean_box(0),
                    v___f_1153_,
                    v___x_1164_,
                    v___x_1163_,
                    v___y_1166_,
                    v___y_1167_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_dec(v___y_1167_);
                v___x_1169_ = crate::leanh::lean_apply_2(
                    v_toPure_1154_,
                    crate::leanh::lean_box(0),
                    v___x_1168_,
                );
                return v___x_1169_;
            }
            2 => {
                v___x_1175_ = lean_nat_dec_le(v___y_1174_, v___x_1172_);
                if v___x_1175_ == 0 {
                    crate::leanh::lean_dec(v___x_1172_);
                    crate::leanh::lean_inc(v___y_1174_);
                    v___y_1166_ = v___y_1174_;
                    v___y_1167_ = v___y_1174_;
                    state = 1;
                    continue;
                } else {
                    v___y_1166_ = v___y_1174_;
                    v___y_1167_ = v___x_1172_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getErrorExplanations___redArg(
    mut v_inst_1180_: *mut crate::leanh::LeanObject,
    mut v_inst_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1182_ = crate::leanh::lean_ctor_get(v_inst_1180_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1182_);
    v_toBind_1183_ = crate::leanh::lean_ctor_get(v_inst_1180_, 1);
    crate::leanh::lean_inc(v_toBind_1183_);
    crate::leanh::lean_dec_ref(v_inst_1180_);
    v_getEnv_1184_ = crate::leanh::lean_ctor_get(v_inst_1181_, 0);
    crate::leanh::lean_inc(v_getEnv_1184_);
    crate::leanh::lean_dec_ref(v_inst_1181_);
    v_toPure_1185_ = crate::leanh::lean_ctor_get(v_toApplicative_1182_, 1);
    crate::leanh::lean_inc(v_toPure_1185_);
    crate::leanh::lean_dec_ref(v_toApplicative_1182_);
    v___f_1186_ = l_Lean_getErrorExplanations___redArg___closed__0;
    v___f_1187_ = l_Lean_getErrorExplanations___redArg___closed__1;
    v___x_1188_ = crate::leanh::lean_box(1);
    v___f_1189_ = crate::leanh::lean_alloc_closure(
        l_Lean_getErrorExplanations___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1189_, 0, v___x_1188_);
    crate::leanh::lean_closure_set(v___f_1189_, 1, v___f_1187_);
    crate::leanh::lean_closure_set(v___f_1189_, 2, v___f_1186_);
    crate::leanh::lean_closure_set(v___f_1189_, 3, v_toPure_1185_);
    v___x_1190_ = crate::leanh::lean_apply_4(
        v_toBind_1183_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1184_,
        v___f_1189_,
    );
    return v___x_1190_;
}
pub unsafe fn l_Lean_getErrorExplanations(
    mut v_m_1191_: *mut crate::leanh::LeanObject,
    mut v_inst_1192_: *mut crate::leanh::LeanObject,
    mut v_inst_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1194_ = l_Lean_getErrorExplanations___redArg(v_inst_1192_, v_inst_1193_);
    return v___x_1194_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(
    mut v_hi_1195_: *mut crate::leanh::LeanObject,
    mut v_pivot_1196_: *mut crate::leanh::LeanObject,
    mut v_as_1197_: *mut crate::leanh::LeanObject,
    mut v_i_1198_: *mut crate::leanh::LeanObject,
    mut v_k_1199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: u8 = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1200_ = lean_nat_dec_lt(v_k_1199_, v_hi_1195_);
                if v___x_1200_ == 0 {
                    crate::leanh::lean_dec(v_k_1199_);
                    crate::leanh::lean_dec_ref(v_pivot_1196_);
                    v___x_1201_ = lean_array_fswap(v_as_1197_, v_i_1198_, v_hi_1195_);
                    v___x_1202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1202_, 0, v_i_1198_);
                    crate::leanh::lean_ctor_set(v___x_1202_, 1, v___x_1201_);
                    return v___x_1202_;
                } else {
                    v___x_1203_ = lean_array_fget_borrowed(v_as_1197_, v_k_1199_);
                    v_fst_1204_ = crate::leanh::lean_ctor_get(v___x_1203_, 0);
                    v_fst_1205_ = crate::leanh::lean_ctor_get(v_pivot_1196_, 0);
                    crate::leanh::lean_inc(v_fst_1204_);
                    v___x_1206_ = l_Lean_Name_toString(v_fst_1204_, v___x_1200_);
                    crate::leanh::lean_inc(v_fst_1205_);
                    v___x_1207_ = l_Lean_Name_toString(v_fst_1205_, v___x_1200_);
                    v___x_1208_ = lean_string_dec_lt(v___x_1206_, v___x_1207_);
                    crate::leanh::lean_dec_ref(v___x_1207_);
                    crate::leanh::lean_dec_ref(v___x_1206_);
                    if v___x_1208_ == 0 {
                        v___x_1209_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1210_ = lean_nat_add(v_k_1199_, v___x_1209_);
                        crate::leanh::lean_dec(v_k_1199_);
                        v_k_1199_ = v___x_1210_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1212_ = lean_array_fswap(v_as_1197_, v_i_1198_, v_k_1199_);
                        v___x_1213_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1214_ = lean_nat_add(v_i_1198_, v___x_1213_);
                        crate::leanh::lean_dec(v_i_1198_);
                        v___x_1215_ = lean_nat_add(v_k_1199_, v___x_1213_);
                        crate::leanh::lean_dec(v_k_1199_);
                        v_as_1197_ = v___x_1212_;
                        v_i_1198_ = v___x_1214_;
                        v_k_1199_ = v___x_1215_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg___boxed(
    mut v_hi_1217_: *mut crate::leanh::LeanObject,
    mut v_pivot_1218_: *mut crate::leanh::LeanObject,
    mut v_as_1219_: *mut crate::leanh::LeanObject,
    mut v_i_1220_: *mut crate::leanh::LeanObject,
    mut v_k_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1222_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(v_hi_1217_, v_pivot_1218_, v_as_1219_, v_i_1220_, v_k_1221_);
    crate::leanh::lean_dec(v_hi_1217_);
    return v_res_1222_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(
    mut v___x_1223_: u8,
    mut v_e_1224_: *mut crate::leanh::LeanObject,
    mut v_e_x27_1225_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: u8 = 0;
    v_fst_1226_ = crate::leanh::lean_ctor_get(v_e_1224_, 0);
    crate::leanh::lean_inc(v_fst_1226_);
    crate::leanh::lean_dec_ref(v_e_1224_);
    v_fst_1227_ = crate::leanh::lean_ctor_get(v_e_x27_1225_, 0);
    crate::leanh::lean_inc(v_fst_1227_);
    crate::leanh::lean_dec_ref(v_e_x27_1225_);
    v___x_1228_ = l_Lean_Name_toString(v_fst_1226_, v___x_1223_);
    v___x_1229_ = l_Lean_Name_toString(v_fst_1227_, v___x_1223_);
    v___x_1230_ = lean_string_dec_lt(v___x_1228_, v___x_1229_);
    crate::leanh::lean_dec_ref(v___x_1229_);
    crate::leanh::lean_dec_ref(v___x_1228_);
    return v___x_1230_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0___boxed(
    mut v___x_1231_: *mut crate::leanh::LeanObject,
    mut v_e_1232_: *mut crate::leanh::LeanObject,
    mut v_e_x27_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_400__boxed_1234_: u8 = 0;
    let mut v_res_1235_: u8 = 0;
    let mut v_r_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_400__boxed_1234_ = (crate::leanh::lean_unbox(v___x_1231_) as u8);
    v_res_1235_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_400__boxed_1234_, v_e_1232_, v_e_x27_1233_);
    v_r_1236_ = crate::leanh::lean_box((v_res_1235_) as usize);
    return v_r_1236_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(
    mut v_n_1237_: *mut crate::leanh::LeanObject,
    mut v_as_1238_: *mut crate::leanh::LeanObject,
    mut v_lo_1239_: *mut crate::leanh::LeanObject,
    mut v_hi_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: u8 = 0;
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: u8 = 0;
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: u8 = 0;
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: u8 = 0;
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1252_ = lean_nat_dec_lt(v_lo_1239_, v_hi_1240_);
                if v___x_1252_ == 0 {
                    crate::leanh::lean_dec(v_lo_1239_);
                    return v_as_1238_;
                } else {
                    v___x_1253_ = lean_nat_add(v_lo_1239_, v_hi_1240_);
                    v___x_1254_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_1255_ = lean_nat_shiftr(v___x_1253_, v___x_1254_);
                    crate::leanh::lean_dec(v___x_1253_);
                    v___x_1268_ = lean_array_fget_borrowed(v_as_1238_, v_mid_1255_);
                    v___x_1269_ = lean_array_fget_borrowed(v_as_1238_, v_lo_1239_);
                    crate::leanh::lean_inc(v___x_1269_);
                    crate::leanh::lean_inc(v___x_1268_);
                    v___x_1270_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_1252_, v___x_1268_, v___x_1269_);
                    if v___x_1270_ == 0 {
                        v___y_1263_ = v_as_1238_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1271_ = lean_array_fswap(v_as_1238_, v_lo_1239_, v_mid_1255_);
                        v___y_1263_ = v___x_1271_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1243_ = lean_array_fget(v___y_1242_, v_hi_1240_);
                crate::leanh::lean_inc_n(v_lo_1239_, 2);
                v___x_1244_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(v_hi_1240_, v_pivot_1243_, v___y_1242_, v_lo_1239_, v_lo_1239_);
                v_fst_1245_ = crate::leanh::lean_ctor_get(v___x_1244_, 0);
                crate::leanh::lean_inc(v_fst_1245_);
                v_snd_1246_ = crate::leanh::lean_ctor_get(v___x_1244_, 1);
                crate::leanh::lean_inc(v_snd_1246_);
                crate::leanh::lean_dec_ref(v___x_1244_);
                v___x_1247_ = lean_nat_dec_le(v_hi_1240_, v_fst_1245_);
                if v___x_1247_ == 0 {
                    v___x_1248_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_n_1237_, v_snd_1246_, v_lo_1239_, v_fst_1245_);
                    v___x_1249_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1250_ = lean_nat_add(v_fst_1245_, v___x_1249_);
                    crate::leanh::lean_dec(v_fst_1245_);
                    v_as_1238_ = v___x_1248_;
                    v_lo_1239_ = v___x_1250_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1245_);
                    crate::leanh::lean_dec(v_lo_1239_);
                    return v_snd_1246_;
                }
            }
            2 => {
                v___x_1258_ = lean_array_fget_borrowed(v___y_1257_, v_mid_1255_);
                v___x_1259_ = lean_array_fget_borrowed(v___y_1257_, v_hi_1240_);
                crate::leanh::lean_inc(v___x_1259_);
                crate::leanh::lean_inc(v___x_1258_);
                v___x_1260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_1252_, v___x_1258_, v___x_1259_);
                if v___x_1260_ == 0 {
                    crate::leanh::lean_dec(v_mid_1255_);
                    v___y_1242_ = v___y_1257_;
                    state = 1;
                    continue;
                } else {
                    v___x_1261_ = lean_array_fswap(v___y_1257_, v_mid_1255_, v_hi_1240_);
                    crate::leanh::lean_dec(v_mid_1255_);
                    v___y_1242_ = v___x_1261_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1264_ = lean_array_fget_borrowed(v___y_1263_, v_hi_1240_);
                v___x_1265_ = lean_array_fget_borrowed(v___y_1263_, v_lo_1239_);
                crate::leanh::lean_inc(v___x_1265_);
                crate::leanh::lean_inc(v___x_1264_);
                v___x_1266_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_1252_, v___x_1264_, v___x_1265_);
                if v___x_1266_ == 0 {
                    v___y_1257_ = v___y_1263_;
                    state = 2;
                    continue;
                } else {
                    v___x_1267_ = lean_array_fswap(v___y_1263_, v_lo_1239_, v_hi_1240_);
                    v___y_1257_ = v___x_1267_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___boxed(
    mut v_n_1272_: *mut crate::leanh::LeanObject,
    mut v_as_1273_: *mut crate::leanh::LeanObject,
    mut v_lo_1274_: *mut crate::leanh::LeanObject,
    mut v_hi_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_n_1272_, v_as_1273_, v_lo_1274_, v_hi_1275_);
    crate::leanh::lean_dec(v_hi_1275_);
    crate::leanh::lean_dec(v_n_1272_);
    return v_res_1276_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(
    mut v_init_1277_: *mut crate::leanh::LeanObject,
    mut v_x_1278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1278_) == 0 {
                    v_k_1279_ = crate::leanh::lean_ctor_get(v_x_1278_, 1);
                    v_v_1280_ = crate::leanh::lean_ctor_get(v_x_1278_, 2);
                    v_l_1281_ = crate::leanh::lean_ctor_get(v_x_1278_, 3);
                    v_r_1282_ = crate::leanh::lean_ctor_get(v_x_1278_, 4);
                    v___x_1283_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_1277_, v_l_1281_);
                    crate::leanh::lean_inc(v_v_1280_);
                    crate::leanh::lean_inc(v_k_1279_);
                    v___x_1284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1284_, 0, v_k_1279_);
                    crate::leanh::lean_ctor_set(v___x_1284_, 1, v_v_1280_);
                    v___x_1285_ = lean_array_push(v___x_1283_, v___x_1284_);
                    v_init_1277_ = v___x_1285_;
                    v_x_1278_ = v_r_1282_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1277_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0___boxed(
    mut v_init_1287_: *mut crate::leanh::LeanObject,
    mut v_x_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_1287_, v_x_1288_);
    crate::leanh::lean_dec(v_x_1288_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_getErrorExplanationsRaw(
    mut v_env_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u8 = 0;
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1291_ = l_Lean_errorExplanationExt;
                v_toEnvExtension_1292_ = crate::leanh::lean_ctor_get(v___x_1291_, 0);
                v_asyncMode_1293_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1292_, 2);
                v___x_1294_ = crate::leanh::lean_box(1);
                v___x_1295_ = crate::leanh::lean_box(0);
                v___x_1296_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_1294_,
                    v___x_1291_,
                    v_env_1290_,
                    v_asyncMode_1293_,
                    v___x_1295_,
                );
                v___x_1297_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1298_ = l_Lean_getErrorExplanations___redArg___lam__2___closed__0;
                v___x_1299_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v___x_1298_, v___x_1296_);
                crate::leanh::lean_dec(v___x_1296_);
                v___x_1300_ = lean_array_get_size(v___x_1299_);
                v___x_1301_ = lean_nat_dec_eq(v___x_1300_, v___x_1297_);
                if v___x_1301_ == 0 {
                    v___x_1302_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1303_ = lean_nat_sub(v___x_1300_, v___x_1302_);
                    v___x_1309_ = lean_nat_dec_le(v___x_1297_, v___x_1303_);
                    if v___x_1309_ == 0 {
                        crate::leanh::lean_inc(v___x_1303_);
                        v___y_1305_ = v___x_1303_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1305_ = v___x_1297_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1299_;
                }
            }
            1 => {
                v___x_1306_ = lean_nat_dec_le(v___y_1305_, v___x_1303_);
                if v___x_1306_ == 0 {
                    crate::leanh::lean_dec(v___x_1303_);
                    crate::leanh::lean_inc(v___y_1305_);
                    v___x_1307_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v___x_1300_, v___x_1299_, v___y_1305_, v___y_1305_);
                    crate::leanh::lean_dec(v___y_1305_);
                    return v___x_1307_;
                } else {
                    v___x_1308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v___x_1300_, v___x_1299_, v___y_1305_, v___x_1303_);
                    crate::leanh::lean_dec(v___x_1303_);
                    return v___x_1308_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(
    mut v_init_1310_: *mut crate::leanh::LeanObject,
    mut v_t_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_1310_, v_t_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0___boxed(
    mut v_init_1313_: *mut crate::leanh::LeanObject,
    mut v_t_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1315_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(
        v_init_1313_,
        v_t_1314_,
    );
    crate::leanh::lean_dec(v_t_1314_);
    return v_res_1315_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(
    mut v_n_1316_: *mut crate::leanh::LeanObject,
    mut v_as_1317_: *mut crate::leanh::LeanObject,
    mut v_lo_1318_: *mut crate::leanh::LeanObject,
    mut v_hi_1319_: *mut crate::leanh::LeanObject,
    mut v_w_1320_: *mut crate::leanh::LeanObject,
    mut v_hlo_1321_: *mut crate::leanh::LeanObject,
    mut v_hhi_1322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1323_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_n_1316_, v_as_1317_, v_lo_1318_, v_hi_1319_);
    return v___x_1323_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___boxed(
    mut v_n_1324_: *mut crate::leanh::LeanObject,
    mut v_as_1325_: *mut crate::leanh::LeanObject,
    mut v_lo_1326_: *mut crate::leanh::LeanObject,
    mut v_hi_1327_: *mut crate::leanh::LeanObject,
    mut v_w_1328_: *mut crate::leanh::LeanObject,
    mut v_hlo_1329_: *mut crate::leanh::LeanObject,
    mut v_hhi_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1331_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(v_n_1324_, v_as_1325_, v_lo_1326_, v_hi_1327_, v_w_1328_, v_hlo_1329_, v_hhi_1330_);
    crate::leanh::lean_dec(v_hi_1327_);
    crate::leanh::lean_dec(v_n_1324_);
    return v_res_1331_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2(
    mut v_n_1332_: *mut crate::leanh::LeanObject,
    mut v_lo_1333_: *mut crate::leanh::LeanObject,
    mut v_hi_1334_: *mut crate::leanh::LeanObject,
    mut v_hhi_1335_: *mut crate::leanh::LeanObject,
    mut v_pivot_1336_: *mut crate::leanh::LeanObject,
    mut v_as_1337_: *mut crate::leanh::LeanObject,
    mut v_i_1338_: *mut crate::leanh::LeanObject,
    mut v_k_1339_: *mut crate::leanh::LeanObject,
    mut v_ilo_1340_: *mut crate::leanh::LeanObject,
    mut v_ik_1341_: *mut crate::leanh::LeanObject,
    mut v_w_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(v_hi_1334_, v_pivot_1336_, v_as_1337_, v_i_1338_, v_k_1339_);
    return v___x_1343_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___boxed(
    mut v_n_1344_: *mut crate::leanh::LeanObject,
    mut v_lo_1345_: *mut crate::leanh::LeanObject,
    mut v_hi_1346_: *mut crate::leanh::LeanObject,
    mut v_hhi_1347_: *mut crate::leanh::LeanObject,
    mut v_pivot_1348_: *mut crate::leanh::LeanObject,
    mut v_as_1349_: *mut crate::leanh::LeanObject,
    mut v_i_1350_: *mut crate::leanh::LeanObject,
    mut v_k_1351_: *mut crate::leanh::LeanObject,
    mut v_ilo_1352_: *mut crate::leanh::LeanObject,
    mut v_ik_1353_: *mut crate::leanh::LeanObject,
    mut v_w_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1355_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2(v_n_1344_, v_lo_1345_, v_hi_1346_, v_hhi_1347_, v_pivot_1348_, v_as_1349_, v_i_1350_, v_k_1351_, v_ilo_1352_, v_ik_1353_, v_w_1354_);
    crate::leanh::lean_dec(v_hi_1346_);
    crate::leanh::lean_dec(v_lo_1345_);
    crate::leanh::lean_dec(v_n_1344_);
    return v_res_1355_;
}
pub unsafe fn l_Lean_getErrorExplanationsSorted___redArg(
    mut v_inst_1356_: *mut crate::leanh::LeanObject,
    mut v_inst_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = l_Lean_getErrorExplanations___redArg(v_inst_1356_, v_inst_1357_);
    return v___x_1358_;
}
pub unsafe fn l_Lean_getErrorExplanationsSorted(
    mut v_m_1359_: *mut crate::leanh::LeanObject,
    mut v_inst_1360_: *mut crate::leanh::LeanObject,
    mut v_inst_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1362_ = l_Lean_getErrorExplanations___redArg(v_inst_1360_, v_inst_1361_);
    return v___x_1362_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ErrorExplanation(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Links(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_errorExplanationExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_errorExplanationExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ErrorExplanation(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ErrorExplanation(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_DocString_Links(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ErrorExplanation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ErrorExplanation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_ErrorExplanation(builtin);
}

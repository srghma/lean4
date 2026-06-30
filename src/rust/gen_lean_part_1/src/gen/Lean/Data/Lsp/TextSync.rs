// Lean compiler output
// Module: Lean.Data.Lsp.TextSync
// Imports: Lean.Data.Lsp.Basic
use crate::ffi::{
    lean_array_size, lean_array_to_list, lean_array_uget, lean_array_uget_borrowed,
    lean_array_uset, lean_nat_dec_eq, lean_string_append, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getBool_x3f, l_Lean_Json_getNat_x3f, l_Lean_Json_getObjValD,
    l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj, l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::l_Lean_Json_getObjValAs_x3f___redArg;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::Basic::{
    initialize_Lean_Data_Lsp_Basic, l_Lean_Lsp_instFromJsonDocumentFilter_fromJson,
    l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson,
    l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson,
    l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson,
    l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson,
    l_Lean_Lsp_instToJsonTextDocumentItem_toJson,
    l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson,
    runtime_initialize_Lean_Data_Lsp_Basic,
};
use crate::r#gen::Lean::Data::Lsp::BasicAux::{
    l_Lean_Lsp_instFromJsonRange_fromJson, l_Lean_Lsp_instToJsonRange_toJson,
};
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0_value:
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
        117, 110, 107, 110, 111, 119, 110, 32, 84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110,
        116, 83, 121, 110, 99, 75, 105, 110, 100, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [116, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 0],
};
static mut l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1_value:
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
static mut l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidOpenTextDocumentParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value:
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
    m_data: [76, 115, 112, 0],
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        68, 105, 100, 79, 112, 101, 110, 84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116,
        80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2_value
) as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2_value
        ) as *mut leanh::LeanObject,
        1777096150718724193 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
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
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0_value)
            as *mut leanh::LeanObject,
        18338692295241883607 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
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
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 111, 99, 117, 109, 101, 110, 116, 83, 101, 108, 101, 99, 116, 111, 114, 0]};
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 67, 104, 97, 110, 103, 101, 82, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 79, 112, 116, 105, 111, 110, 115, 0]};
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1_value
) as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value) as *mut leanh::LeanObject,6773744487318448338 as *mut leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1_value) as *mut leanh::LeanObject,17376441392313824390 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 111, 99, 117, 109, 101, 110, 116, 83, 101, 108, 101, 99, 116, 111, 114, 63, 0]};
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5_value) as *mut leanh::LeanObject,14662850476098908763 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 121, 110, 99, 75, 105, 110, 100, 0]};
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10_value) as *mut leanh::LeanObject,9751881898413921770 as *mut leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 120, 116, 0],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1_value:
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
    m_data: [114, 97, 110, 103, 101, 0],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonRange_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1_value:
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
    m_fun: l_Lean_Json_getStr_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0_value:
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
    m_fun: l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        99, 111, 110, 116, 101, 110, 116, 67, 104, 97, 110, 103, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidChangeTextDocumentParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        68, 105, 100, 67, 104, 97, 110, 103, 101, 84, 101, 120, 116, 68, 111, 99, 117, 109, 101,
        110, 116, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        17982117513186199655 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6_value:
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
            l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value
        ) as *mut leanh::LeanObject,
        17232133447220150647 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidSaveTextDocumentParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        68, 105, 100, 83, 97, 118, 101, 84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116,
        80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        12587282521778334376 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6_value:
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
    m_data: [116, 101, 120, 116, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7_value:
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
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6_value
        ) as *mut leanh::LeanObject,
        2082988283416480631 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [105, 110, 99, 108, 117, 100, 101, 84, 101, 120, 116, 0],
};
static mut l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonSaveOptions___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Lsp_instToJsonSaveOptions_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonSaveOptions___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonSaveOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonSaveOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonSaveOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [83, 97, 118, 101, 79, 112, 116, 105, 111, 110, 115, 0],
};
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
        9731365713045262675 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0_value)
            as *mut leanh::LeanObject,
        15217983757875996411 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonSaveOptions___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonSaveOptions_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonSaveOptions___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonSaveOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDidCloseTextDocumentParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidCloseTextDocumentParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        68, 105, 100, 67, 108, 111, 115, 101, 84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110,
        116, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        308332401153831253 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0_value:
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
    m_data: [111, 112, 101, 110, 67, 108, 111, 115, 101, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1_value:
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
    m_data: [99, 104, 97, 110, 103, 101, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2_value:
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
    m_data: [119, 105, 108, 108, 83, 97, 118, 101, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        119, 105, 108, 108, 83, 97, 118, 101, 87, 97, 105, 116, 85, 110, 116, 105, 108, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 97, 118, 101, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0_value:
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
        84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 83, 121, 110, 99, 79, 112, 116,
        105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        4958612648835839449 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0_value)
            as *mut leanh::LeanObject,
        9134419134227876233 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1_value)
            as *mut leanh::LeanObject,
        13755659578849458301 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2_value)
            as *mut leanh::LeanObject,
        12861593690867574868 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3_value)
            as *mut leanh::LeanObject,
        15946133124393108346 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20_value:
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
    m_data: [115, 97, 118, 101, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21_value:
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
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20_value
        ) as *mut leanh::LeanObject,
        12047597270034623148 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(
    mut v_x_1308_: u8,
) -> *mut leanh::LeanObject {
    match v_x_1308_ {
        0 => {
            let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1309_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1309_;
        }
        1 => {
            let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1310_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1310_;
        }
        _ => {
            let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1311_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1311_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___boxed(
    mut v_x_1312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1313_: u8 = 0;
    let mut v_res_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1313_ = (leanh::lean_unbox(v_x_1312_) as u8);
    v_res_1314_ = l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(v_x_boxed_1313_);
    return v_res_1314_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx(
    mut v_x_1315_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1316_ = l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(v_x_1315_);
    return v___x_1316_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx___boxed(
    mut v_x_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_1318_: u8 = 0;
    let mut v_res_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1318_ = (leanh::lean_unbox(v_x_1317_) as u8);
    v_res_1319_ = l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx(v_x_4__boxed_1318_);
    return v_res_1319_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(
    mut v_k_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1320_);
    return v_k_1320_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg___boxed(
    mut v_k_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(v_k_1321_);
    leanh::lean_dec(v_k_1321_);
    return v_res_1322_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorElim(
    mut v_motive_1323_: *mut leanh::LeanObject,
    mut v_ctorIdx_1324_: *mut leanh::LeanObject,
    mut v_t_1325_: u8,
    mut v_h_1326_: *mut leanh::LeanObject,
    mut v_k_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1327_);
    return v_k_1327_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorElim___boxed(
    mut v_motive_1328_: *mut leanh::LeanObject,
    mut v_ctorIdx_1329_: *mut leanh::LeanObject,
    mut v_t_1330_: *mut leanh::LeanObject,
    mut v_h_1331_: *mut leanh::LeanObject,
    mut v_k_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1333_: u8 = 0;
    let mut v_res_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1333_ = (leanh::lean_unbox(v_t_1330_) as u8);
    v_res_1334_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim(
        v_motive_1328_,
        v_ctorIdx_1329_,
        v_t_boxed_1333_,
        v_h_1331_,
        v_k_1332_,
    );
    leanh::lean_dec(v_k_1332_);
    leanh::lean_dec(v_ctorIdx_1329_);
    return v_res_1334_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(
    mut v_none_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_none_1335_);
    return v_none_1335_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg___boxed(
    mut v_none_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1337_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(v_none_1336_);
    leanh::lean_dec(v_none_1336_);
    return v_res_1337_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_none_elim(
    mut v_motive_1338_: *mut leanh::LeanObject,
    mut v_t_1339_: u8,
    mut v_h_1340_: *mut leanh::LeanObject,
    mut v_none_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_none_1341_);
    return v_none_1341_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_none_elim___boxed(
    mut v_motive_1342_: *mut leanh::LeanObject,
    mut v_t_1343_: *mut leanh::LeanObject,
    mut v_h_1344_: *mut leanh::LeanObject,
    mut v_none_1345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1346_: u8 = 0;
    let mut v_res_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1346_ = (leanh::lean_unbox(v_t_1343_) as u8);
    v_res_1347_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim(
        v_motive_1342_,
        v_t_boxed_1346_,
        v_h_1344_,
        v_none_1345_,
    );
    leanh::lean_dec(v_none_1345_);
    return v_res_1347_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(
    mut v_full_1348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_full_1348_);
    return v_full_1348_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg___boxed(
    mut v_full_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1350_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(v_full_1349_);
    leanh::lean_dec(v_full_1349_);
    return v_res_1350_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_full_elim(
    mut v_motive_1351_: *mut leanh::LeanObject,
    mut v_t_1352_: u8,
    mut v_h_1353_: *mut leanh::LeanObject,
    mut v_full_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_full_1354_);
    return v_full_1354_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_full_elim___boxed(
    mut v_motive_1355_: *mut leanh::LeanObject,
    mut v_t_1356_: *mut leanh::LeanObject,
    mut v_h_1357_: *mut leanh::LeanObject,
    mut v_full_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1359_: u8 = 0;
    let mut v_res_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1359_ = (leanh::lean_unbox(v_t_1356_) as u8);
    v_res_1360_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim(
        v_motive_1355_,
        v_t_boxed_1359_,
        v_h_1357_,
        v_full_1358_,
    );
    leanh::lean_dec(v_full_1358_);
    return v_res_1360_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(
    mut v_incremental_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_incremental_1361_);
    return v_incremental_1361_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg___boxed(
    mut v_incremental_1362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1363_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(v_incremental_1362_);
    leanh::lean_dec(v_incremental_1362_);
    return v_res_1363_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(
    mut v_motive_1364_: *mut leanh::LeanObject,
    mut v_t_1365_: u8,
    mut v_h_1366_: *mut leanh::LeanObject,
    mut v_incremental_1367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_incremental_1367_);
    return v_incremental_1367_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___boxed(
    mut v_motive_1368_: *mut leanh::LeanObject,
    mut v_t_1369_: *mut leanh::LeanObject,
    mut v_h_1370_: *mut leanh::LeanObject,
    mut v_incremental_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1372_: u8 = 0;
    let mut v_res_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1372_ = (leanh::lean_unbox(v_t_1369_) as u8);
    v_res_1373_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(
        v_motive_1368_,
        v_t_boxed_1372_,
        v_h_1370_,
        v_incremental_1371_,
    );
    leanh::lean_dec(v_incremental_1371_);
    return v_res_1373_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0(
    mut v_j_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1389_ = l_Lean_Json_getNat_x3f(v_j_1386_);
                if leanh::lean_obj_tag(v___x_1389_) == 1 {
                    v_a_1390_ = leanh::lean_ctor_get(v___x_1389_, 0);
                    leanh::lean_inc(v_a_1390_);
                    leanh::lean_dec_ref_known(v___x_1389_, 1);
                    v___x_1391_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1392_ = lean_nat_dec_eq(v_a_1390_, v___x_1391_);
                    if v___x_1392_ == 0 {
                        v___x_1393_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1394_ = lean_nat_dec_eq(v_a_1390_, v___x_1393_);
                        if v___x_1394_ == 0 {
                            v___x_1395_ = leanh::lean_unsigned_to_nat(2);
                            v___x_1396_ = lean_nat_dec_eq(v_a_1390_, v___x_1395_);
                            leanh::lean_dec(v_a_1390_);
                            if v___x_1396_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_1397_ = l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2;
                                return v___x_1397_;
                            }
                        } else {
                            leanh::lean_dec(v_a_1390_);
                            v___x_1398_ =
                                l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3;
                            return v___x_1398_;
                        }
                    } else {
                        leanh::lean_dec(v_a_1390_);
                        v___x_1399_ =
                            l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4;
                        return v___x_1399_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1389_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1388_ = l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1;
                return v___x_1388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ = leanh::lean_unsigned_to_nat(0);
    v___x_1403_ = l_Lean_JsonNumber_fromNat(v___x_1402_);
    return v___x_1403_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0_once
        ),
        _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0,
    );
    v___x_1405_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1405_, 0, v___x_1404_);
    return v___x_1405_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1406_ = leanh::lean_unsigned_to_nat(1);
    v___x_1407_ = l_Lean_JsonNumber_fromNat(v___x_1406_);
    return v___x_1407_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2_once
        ),
        _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2,
    );
    v___x_1409_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1409_, 0, v___x_1408_);
    return v___x_1409_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = leanh::lean_unsigned_to_nat(2);
    v___x_1411_ = l_Lean_JsonNumber_fromNat(v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1412_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4_once
        ),
        _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4,
    );
    v___x_1413_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1413_, 0, v___x_1412_);
    return v___x_1413_;
}
pub unsafe fn l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(
    mut v_x_1414_: u8,
) -> *mut leanh::LeanObject {
    match v_x_1414_ {
        0 => {
            let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1415_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once
                ),
                _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1,
            );
            return v___x_1415_;
        }
        1 => {
            let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1416_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once
                ),
                _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3,
            );
            return v___x_1416_;
        }
        _ => {
            let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1417_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once
                ),
                _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5,
            );
            return v___x_1417_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___boxed(
    mut v_x_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_81__boxed_1419_: u8 = 0;
    let mut v_res_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_81__boxed_1419_ = (leanh::lean_unbox(v_x_1418_) as u8);
    v_res_1420_ = l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(v_x_81__boxed_1419_);
    return v_res_1420_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(
    mut v_a_1423_: *mut leanh::LeanObject,
    mut v_a_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1423_) == 0 {
                    v___x_1425_ = lean_array_to_list(v_a_1424_);
                    return v___x_1425_;
                } else {
                    v_head_1426_ = leanh::lean_ctor_get(v_a_1423_, 0);
                    leanh::lean_inc(v_head_1426_);
                    v_tail_1427_ = leanh::lean_ctor_get(v_a_1423_, 1);
                    leanh::lean_inc(v_tail_1427_);
                    leanh::lean_dec_ref_known(v_a_1423_, 2);
                    v___x_1428_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_1424_,
                        v_head_1426_,
                    );
                    v_a_1423_ = v_tail_1427_;
                    v_a_1424_ = v___x_1428_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson(
    mut v_x_1433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
    v___x_1435_ = l_Lean_Lsp_instToJsonTextDocumentItem_toJson(v_x_1433_);
    v___x_1436_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1436_, 0, v___x_1434_);
    leanh::lean_ctor_set(v___x_1436_, 1, v___x_1435_);
    v___x_1437_ = leanh::lean_box(0);
    v___x_1438_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1438_, 0, v___x_1436_);
    leanh::lean_ctor_set(v___x_1438_, 1, v___x_1437_);
    v___x_1439_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1439_, 0, v___x_1438_);
    leanh::lean_ctor_set(v___x_1439_, 1, v___x_1437_);
    v___x_1440_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
    v___x_1441_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_1439_, v___x_1440_);
    v___x_1442_ = l_Lean_Json_mkObj(v___x_1441_);
    leanh::lean_dec(v___x_1441_);
    return v___x_1442_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(
    mut v_j_1445_: *mut leanh::LeanObject,
    mut v_k_1446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1447_ = l_Lean_Json_getObjValD(v_j_1445_, v_k_1446_);
    v___x_1448_ = l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(v___x_1447_);
    return v___x_1448_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0___boxed(
    mut v_j_1449_: *mut leanh::LeanObject,
    mut v_k_1450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1451_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(v_j_1449_, v_k_1450_);
    leanh::lean_dec_ref(v_k_1450_);
    return v_res_1451_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = 1;
    v___x_1460_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3;
    v___x_1461_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1460_, v___x_1459_);
    return v___x_1461_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_1464_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4,
    );
    v___x_1465_ = lean_string_append(v___x_1464_, v___x_1463_);
    return v___x_1465_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1468_ = 1;
    v___x_1469_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7;
    v___x_1470_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1469_, v___x_1468_);
    return v___x_1470_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1471_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8,
    );
    v___x_1472_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6,
    );
    v___x_1473_ = lean_string_append(v___x_1472_, v___x_1471_);
    return v___x_1473_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1475_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_1476_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9,
    );
    v___x_1477_ = lean_string_append(v___x_1476_, v___x_1475_);
    return v___x_1477_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson(
    mut v_json_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v_a_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1494_: u8 = 0;
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut v_a_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1479_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                v___x_1480_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(v_json_1478_, v___x_1479_);
                if leanh::lean_obj_tag(v___x_1480_) == 0 {
                    v_a_1481_ = leanh::lean_ctor_get(v___x_1480_, 0);
                    v_isSharedCheck_1490_ = (!leanh::lean_is_exclusive(v___x_1480_)) as u8;
                    if v_isSharedCheck_1490_ == 0 {
                        v___x_1483_ = v___x_1480_;
                        v_isShared_1484_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1481_);
                        leanh::lean_dec(v___x_1480_);
                        v___x_1483_ = leanh::lean_box(0);
                        v_isShared_1484_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_1480_) == 0 {
                        v_a_1491_ = leanh::lean_ctor_get(v___x_1480_, 0);
                        v_isSharedCheck_1498_ =
                            (!leanh::lean_is_exclusive(v___x_1480_)) as u8;
                        if v_isSharedCheck_1498_ == 0 {
                            v___x_1493_ = v___x_1480_;
                            v_isShared_1494_ = v_isSharedCheck_1498_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1491_);
                            leanh::lean_dec(v___x_1480_);
                            v___x_1493_ = leanh::lean_box(0);
                            v_isShared_1494_ = v_isSharedCheck_1498_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1499_ = leanh::lean_ctor_get(v___x_1480_, 0);
                        v_isSharedCheck_1506_ =
                            (!leanh::lean_is_exclusive(v___x_1480_)) as u8;
                        if v_isSharedCheck_1506_ == 0 {
                            v___x_1501_ = v___x_1480_;
                            v_isShared_1502_ = v_isSharedCheck_1506_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1499_);
                            leanh::lean_dec(v___x_1480_);
                            v___x_1501_ = leanh::lean_box(0);
                            v_isShared_1502_ = v_isSharedCheck_1506_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1485_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11,
                );
                v___x_1486_ = lean_string_append(v___x_1485_, v_a_1481_);
                leanh::lean_dec(v_a_1481_);
                if v_isShared_1484_ == 0 {
                    leanh::lean_ctor_set(v___x_1483_, 0, v___x_1486_);
                    v___x_1488_ = v___x_1483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1489_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
                    v___x_1488_ = v_reuseFailAlloc_1489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1488_;
            }
            3 => {
                if v_isShared_1494_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1493_, 0);
                    v___x_1496_ = v___x_1493_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1497_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
                    v___x_1496_ = v_reuseFailAlloc_1497_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1496_;
            }
            5 => {
                if v_isShared_1502_ == 0 {
                    v___x_1504_ = v___x_1501_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
                    v___x_1504_ = v_reuseFailAlloc_1505_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(
    mut v_j_1509_: *mut leanh::LeanObject,
    mut v_k_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: u8 = 0;
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: u8 = 0;
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1513_ = l_Lean_Json_getObjValD(v_j_1509_, v_k_1510_);
                v___x_1514_ = l_Lean_Json_getNat_x3f(v___x_1513_);
                if leanh::lean_obj_tag(v___x_1514_) == 1 {
                    v_a_1515_ = leanh::lean_ctor_get(v___x_1514_, 0);
                    leanh::lean_inc(v_a_1515_);
                    leanh::lean_dec_ref_known(v___x_1514_, 1);
                    v___x_1516_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1517_ = lean_nat_dec_eq(v_a_1515_, v___x_1516_);
                    if v___x_1517_ == 0 {
                        v___x_1518_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1519_ = lean_nat_dec_eq(v_a_1515_, v___x_1518_);
                        if v___x_1519_ == 0 {
                            v___x_1520_ = leanh::lean_unsigned_to_nat(2);
                            v___x_1521_ = lean_nat_dec_eq(v_a_1515_, v___x_1520_);
                            leanh::lean_dec(v_a_1515_);
                            if v___x_1521_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_1522_ = l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2;
                                return v___x_1522_;
                            }
                        } else {
                            leanh::lean_dec(v_a_1515_);
                            v___x_1523_ =
                                l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3;
                            return v___x_1523_;
                        }
                    } else {
                        leanh::lean_dec(v_a_1515_);
                        v___x_1524_ =
                            l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4;
                        return v___x_1524_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1514_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1512_ = l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1;
                return v___x_1512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1___boxed(
    mut v_j_1525_: *mut leanh::LeanObject,
    mut v_k_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1527_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_j_1525_, v_k_1526_);
    leanh::lean_dec_ref(v_k_1526_);
    return v_res_1527_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(
    mut v_sz_1528_: usize,
    mut v_i_1529_: usize,
    mut v_bs_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: u8 = 0;
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut v_a_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: usize = 0;
    let mut v___x_1547_: usize = 0;
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1531_ = lean_usize_dec_lt(v_i_1529_, v_sz_1528_);
                if v___x_1531_ == 0 {
                    v___x_1532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1532_, 0, v_bs_1530_);
                    return v___x_1532_;
                } else {
                    v_v_1533_ = lean_array_uget_borrowed(v_bs_1530_, v_i_1529_);
                    leanh::lean_inc(v_v_1533_);
                    v___x_1534_ = l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(v_v_1533_);
                    if leanh::lean_obj_tag(v___x_1534_) == 0 {
                        leanh::lean_dec_ref(v_bs_1530_);
                        v_a_1535_ = leanh::lean_ctor_get(v___x_1534_, 0);
                        v_isSharedCheck_1542_ =
                            (!leanh::lean_is_exclusive(v___x_1534_)) as u8;
                        if v_isSharedCheck_1542_ == 0 {
                            v___x_1537_ = v___x_1534_;
                            v_isShared_1538_ = v_isSharedCheck_1542_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1535_);
                            leanh::lean_dec(v___x_1534_);
                            v___x_1537_ = leanh::lean_box(0);
                            v_isShared_1538_ = v_isSharedCheck_1542_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1543_ = leanh::lean_ctor_get(v___x_1534_, 0);
                        leanh::lean_inc(v_a_1543_);
                        leanh::lean_dec_ref_known(v___x_1534_, 1);
                        v___x_1544_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1545_ = lean_array_uset(v_bs_1530_, v_i_1529_, v___x_1544_);
                        v___x_1546_ = 1usize;
                        v___x_1547_ = lean_usize_add(v_i_1529_, v___x_1546_);
                        v___x_1548_ = lean_array_uset(v_bs_x27_1545_, v_i_1529_, v_a_1543_);
                        v_i_1529_ = v___x_1547_;
                        v_bs_1530_ = v___x_1548_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1538_ == 0 {
                    v___x_1540_ = v___x_1537_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1541_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
                    v___x_1540_ = v_reuseFailAlloc_1541_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_sz_1550_: *mut leanh::LeanObject,
    mut v_i_1551_: *mut leanh::LeanObject,
    mut v_bs_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1553_: usize = 0;
    let mut v_i_boxed_1554_: usize = 0;
    let mut v_res_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1553_ = leanh::lean_unbox_usize(v_sz_1550_);
    leanh::lean_dec(v_sz_1550_);
    v_i_boxed_1554_ = leanh::lean_unbox_usize(v_i_1551_);
    leanh::lean_dec(v_i_1551_);
    v_res_1555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_boxed_1553_, v_i_boxed_1554_, v_bs_1552_);
    return v_res_1555_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(
    mut v_x_1558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1558_) == 4 {
        let mut v_elems_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1560_: usize = 0;
        let mut v___x_1561_: usize = 0;
        let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_1559_ = leanh::lean_ctor_get(v_x_1558_, 0);
        leanh::lean_inc_ref(v_elems_1559_);
        leanh::lean_dec_ref_known(v_x_1558_, 1);
        v_sz_1560_ = lean_array_size(v_elems_1559_);
        v___x_1561_ = 0usize;
        v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_1560_, v___x_1561_, v_elems_1559_);
        return v___x_1562_;
    } else {
        let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1563_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0;
        v___x_1564_ = leanh::lean_unsigned_to_nat(80);
        v___x_1565_ = l_Lean_Json_pretty(v_x_1558_, v___x_1564_);
        v___x_1566_ = lean_string_append(v___x_1563_, v___x_1565_);
        leanh::lean_dec_ref(v___x_1565_);
        v___x_1567_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1;
        v___x_1568_ = lean_string_append(v___x_1566_, v___x_1567_);
        v___x_1569_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1569_, 0, v___x_1568_);
        return v___x_1569_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(
    mut v_x_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v_a_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1586_: u8 = 0;
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1572_) == 0 {
                    v___x_1573_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0;
                    return v___x_1573_;
                } else {
                    v___x_1574_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(v_x_1572_);
                    if leanh::lean_obj_tag(v___x_1574_) == 0 {
                        v_a_1575_ = leanh::lean_ctor_get(v___x_1574_, 0);
                        v_isSharedCheck_1582_ =
                            (!leanh::lean_is_exclusive(v___x_1574_)) as u8;
                        if v_isSharedCheck_1582_ == 0 {
                            v___x_1577_ = v___x_1574_;
                            v_isShared_1578_ = v_isSharedCheck_1582_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1575_);
                            leanh::lean_dec(v___x_1574_);
                            v___x_1577_ = leanh::lean_box(0);
                            v_isShared_1578_ = v_isSharedCheck_1582_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1583_ = leanh::lean_ctor_get(v___x_1574_, 0);
                        v_isSharedCheck_1591_ =
                            (!leanh::lean_is_exclusive(v___x_1574_)) as u8;
                        if v_isSharedCheck_1591_ == 0 {
                            v___x_1585_ = v___x_1574_;
                            v_isShared_1586_ = v_isSharedCheck_1591_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1583_);
                            leanh::lean_dec(v___x_1574_);
                            v___x_1585_ = leanh::lean_box(0);
                            v_isShared_1586_ = v_isSharedCheck_1591_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1578_ == 0 {
                    v___x_1580_ = v___x_1577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
                    v___x_1580_ = v_reuseFailAlloc_1581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1580_;
            }
            3 => {
                v___x_1587_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1587_, 0, v_a_1583_);
                if v_isShared_1586_ == 0 {
                    leanh::lean_ctor_set(v___x_1585_, 0, v___x_1587_);
                    v___x_1589_ = v___x_1585_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1590_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
                    v___x_1589_ = v_reuseFailAlloc_1590_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(
    mut v_j_1592_: *mut leanh::LeanObject,
    mut v_k_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Lean_Json_getObjValD(v_j_1592_, v_k_1593_);
    v___x_1595_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(v___x_1594_);
    return v___x_1595_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0___boxed(
    mut v_j_1596_: *mut leanh::LeanObject,
    mut v_k_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_j_1596_, v_k_1597_);
    leanh::lean_dec_ref(v_k_1597_);
    return v_res_1598_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = 1;
    v___x_1606_ = l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2;
    v___x_1607_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1606_, v___x_1605_);
    return v___x_1607_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_1609_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3,
    );
    v___x_1610_ = lean_string_append(v___x_1609_, v___x_1608_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = 1;
    v___x_1615_ = l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6;
    v___x_1616_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1615_, v___x_1614_);
    return v___x_1616_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7,
    );
    v___x_1618_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4,
    );
    v___x_1619_ = lean_string_append(v___x_1618_, v___x_1617_);
    return v___x_1619_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_1621_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8,
    );
    v___x_1622_ = lean_string_append(v___x_1621_, v___x_1620_);
    return v___x_1622_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = 1;
    v___x_1627_ =
        l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11;
    v___x_1628_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1627_, v___x_1626_);
    return v___x_1628_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12,
    );
    v___x_1630_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4,
    );
    v___x_1631_ = lean_string_append(v___x_1630_, v___x_1629_);
    return v___x_1631_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_1633_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13,
    );
    v___x_1634_ = lean_string_append(v___x_1633_, v___x_1632_);
    return v___x_1634_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson(
    mut v_json_1635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut v_a_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1655_: u8 = 0;
    let mut v_a_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut v_a_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1676_: u8 = 0;
    let mut v_a_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1636_ = l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0;
                leanh::lean_inc(v_json_1635_);
                v___x_1637_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_json_1635_, v___x_1636_);
                if leanh::lean_obj_tag(v___x_1637_) == 0 {
                    leanh::lean_dec(v_json_1635_);
                    v_a_1638_ = leanh::lean_ctor_get(v___x_1637_, 0);
                    v_isSharedCheck_1647_ = (!leanh::lean_is_exclusive(v___x_1637_)) as u8;
                    if v_isSharedCheck_1647_ == 0 {
                        v___x_1640_ = v___x_1637_;
                        v_isShared_1641_ = v_isSharedCheck_1647_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1638_);
                        leanh::lean_dec(v___x_1637_);
                        v___x_1640_ = leanh::lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1647_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_1637_) == 0 {
                        leanh::lean_dec(v_json_1635_);
                        v_a_1648_ = leanh::lean_ctor_get(v___x_1637_, 0);
                        v_isSharedCheck_1655_ =
                            (!leanh::lean_is_exclusive(v___x_1637_)) as u8;
                        if v_isSharedCheck_1655_ == 0 {
                            v___x_1650_ = v___x_1637_;
                            v_isShared_1651_ = v_isSharedCheck_1655_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1648_);
                            leanh::lean_dec(v___x_1637_);
                            v___x_1650_ = leanh::lean_box(0);
                            v_isShared_1651_ = v_isSharedCheck_1655_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1656_ = leanh::lean_ctor_get(v___x_1637_, 0);
                        leanh::lean_inc(v_a_1656_);
                        leanh::lean_dec_ref_known(v___x_1637_, 1);
                        v___x_1657_ = l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10;
                        v___x_1658_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_1635_, v___x_1657_);
                        if leanh::lean_obj_tag(v___x_1658_) == 0 {
                            leanh::lean_dec(v_a_1656_);
                            v_a_1659_ = leanh::lean_ctor_get(v___x_1658_, 0);
                            v_isSharedCheck_1668_ =
                                (!leanh::lean_is_exclusive(v___x_1658_)) as u8;
                            if v_isSharedCheck_1668_ == 0 {
                                v___x_1661_ = v___x_1658_;
                                v_isShared_1662_ = v_isSharedCheck_1668_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1659_);
                                leanh::lean_dec(v___x_1658_);
                                v___x_1661_ = leanh::lean_box(0);
                                v_isShared_1662_ = v_isSharedCheck_1668_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_1658_) == 0 {
                                leanh::lean_dec(v_a_1656_);
                                v_a_1669_ = leanh::lean_ctor_get(v___x_1658_, 0);
                                v_isSharedCheck_1676_ =
                                    (!leanh::lean_is_exclusive(v___x_1658_)) as u8;
                                if v_isSharedCheck_1676_ == 0 {
                                    v___x_1671_ = v___x_1658_;
                                    v_isShared_1672_ = v_isSharedCheck_1676_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1669_);
                                    leanh::lean_dec(v___x_1658_);
                                    v___x_1671_ = leanh::lean_box(0);
                                    v_isShared_1672_ = v_isSharedCheck_1676_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_1677_ = leanh::lean_ctor_get(v___x_1658_, 0);
                                v_isSharedCheck_1686_ =
                                    (!leanh::lean_is_exclusive(v___x_1658_)) as u8;
                                if v_isSharedCheck_1686_ == 0 {
                                    v___x_1679_ = v___x_1658_;
                                    v_isShared_1680_ = v_isSharedCheck_1686_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1677_);
                                    leanh::lean_dec(v___x_1658_);
                                    v___x_1679_ = leanh::lean_box(0);
                                    v_isShared_1680_ = v_isSharedCheck_1686_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1642_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9_once), _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9);
                v___x_1643_ = lean_string_append(v___x_1642_, v_a_1638_);
                leanh::lean_dec(v_a_1638_);
                if v_isShared_1641_ == 0 {
                    leanh::lean_ctor_set(v___x_1640_, 0, v___x_1643_);
                    v___x_1645_ = v___x_1640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1646_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
                    v___x_1645_ = v_reuseFailAlloc_1646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1645_;
            }
            3 => {
                if v_isShared_1651_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1650_, 0);
                    v___x_1653_ = v___x_1650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1654_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
                    v___x_1653_ = v_reuseFailAlloc_1654_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1653_;
            }
            5 => {
                v___x_1663_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14_once), _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14);
                v___x_1664_ = lean_string_append(v___x_1663_, v_a_1659_);
                leanh::lean_dec(v_a_1659_);
                if v_isShared_1662_ == 0 {
                    leanh::lean_ctor_set(v___x_1661_, 0, v___x_1664_);
                    v___x_1666_ = v___x_1661_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
                    v___x_1666_ = v_reuseFailAlloc_1667_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1666_;
            }
            7 => {
                if v_isShared_1672_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1671_, 0);
                    v___x_1674_ = v___x_1671_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1675_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
                    v___x_1674_ = v_reuseFailAlloc_1675_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1674_;
            }
            9 => {
                v___x_1681_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1681_, 0, v_a_1656_);
                v___x_1682_ = (leanh::lean_unbox(v_a_1677_) as u8);
                leanh::lean_dec(v_a_1677_);
                leanh::lean_ctor_set_uint8(
                    v___x_1681_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1682_,
                );
                if v_isShared_1680_ == 0 {
                    leanh::lean_ctor_set(v___x_1679_, 0, v___x_1681_);
                    v___x_1684_ = v___x_1679_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1681_);
                    v___x_1684_ = v_reuseFailAlloc_1685_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx(
    mut v_x_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1689_) == 0 {
        let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1690_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1690_;
    } else {
        let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1691_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1691_;
    }
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___boxed(
    mut v_x_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx(v_x_1692_);
    leanh::lean_dec_ref(v_x_1692_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(
    mut v_t_1694_: *mut leanh::LeanObject,
    mut v_k_1695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1694_) == 0 {
        let mut v_range_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_text_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_range_1696_ = leanh::lean_ctor_get(v_t_1694_, 0);
        leanh::lean_inc_ref(v_range_1696_);
        v_text_1697_ = leanh::lean_ctor_get(v_t_1694_, 1);
        leanh::lean_inc_ref(v_text_1697_);
        leanh::lean_dec_ref_known(v_t_1694_, 2);
        v___x_1698_ = leanh::lean_apply_2(v_k_1695_, v_range_1696_, v_text_1697_);
        return v___x_1698_;
    } else {
        let mut v_text_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_text_1699_ = leanh::lean_ctor_get(v_t_1694_, 0);
        leanh::lean_inc_ref(v_text_1699_);
        leanh::lean_dec_ref_known(v_t_1694_, 1);
        v___x_1700_ = leanh::lean_apply_1(v_k_1695_, v_text_1699_);
        return v___x_1700_;
    }
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(
    mut v_motive_1701_: *mut leanh::LeanObject,
    mut v_ctorIdx_1702_: *mut leanh::LeanObject,
    mut v_t_1703_: *mut leanh::LeanObject,
    mut v_h_1704_: *mut leanh::LeanObject,
    mut v_k_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_1703_, v_k_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___boxed(
    mut v_motive_1707_: *mut leanh::LeanObject,
    mut v_ctorIdx_1708_: *mut leanh::LeanObject,
    mut v_t_1709_: *mut leanh::LeanObject,
    mut v_h_1710_: *mut leanh::LeanObject,
    mut v_k_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(
        v_motive_1707_,
        v_ctorIdx_1708_,
        v_t_1709_,
        v_h_1710_,
        v_k_1711_,
    );
    leanh::lean_dec(v_ctorIdx_1708_);
    return v_res_1712_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim___redArg(
    mut v_t_1713_: *mut leanh::LeanObject,
    mut v_rangeChange_1714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ =
        l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_1713_, v_rangeChange_1714_);
    return v___x_1715_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim(
    mut v_motive_1716_: *mut leanh::LeanObject,
    mut v_t_1717_: *mut leanh::LeanObject,
    mut v_h_1718_: *mut leanh::LeanObject,
    mut v_rangeChange_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ =
        l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_1717_, v_rangeChange_1719_);
    return v___x_1720_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim___redArg(
    mut v_t_1721_: *mut leanh::LeanObject,
    mut v_fullChange_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ =
        l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_1721_, v_fullChange_1722_);
    return v___x_1723_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim(
    mut v_motive_1724_: *mut leanh::LeanObject,
    mut v_t_1725_: *mut leanh::LeanObject,
    mut v_h_1726_: *mut leanh::LeanObject,
    mut v_fullChange_1727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ =
        l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_1725_, v_fullChange_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0(
    mut v___x_1731_: *mut leanh::LeanObject,
    mut v___x_1732_: *mut leanh::LeanObject,
    mut v_j_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1744_: u8 = 0;
    let mut v_a_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1753_: u8 = 0;
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1754_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1;
                leanh::lean_inc(v_j_1733_);
                v___x_1755_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_1733_, v___x_1732_, v___x_1754_);
                if leanh::lean_obj_tag(v___x_1755_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1755_, 1);
                    state = 1;
                    continue;
                } else {
                    v_a_1756_ = leanh::lean_ctor_get(v___x_1755_, 0);
                    leanh::lean_inc(v_a_1756_);
                    leanh::lean_dec_ref_known(v___x_1755_, 1);
                    v___x_1757_ =
                        l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                    leanh::lean_inc_ref(v___x_1731_);
                    leanh::lean_inc(v_j_1733_);
                    v___x_1758_ =
                        l_Lean_Json_getObjValAs_x3f___redArg(v_j_1733_, v___x_1731_, v___x_1757_);
                    if leanh::lean_obj_tag(v___x_1758_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1758_, 1);
                        leanh::lean_dec(v_a_1756_);
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_j_1733_);
                        leanh::lean_dec_ref(v___x_1731_);
                        v_a_1759_ = leanh::lean_ctor_get(v___x_1758_, 0);
                        v_isSharedCheck_1767_ =
                            (!leanh::lean_is_exclusive(v___x_1758_)) as u8;
                        if v_isSharedCheck_1767_ == 0 {
                            v___x_1761_ = v___x_1758_;
                            v_isShared_1762_ = v_isSharedCheck_1767_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1759_);
                            leanh::lean_dec(v___x_1758_);
                            v___x_1761_ = leanh::lean_box(0);
                            v_isShared_1762_ = v_isSharedCheck_1767_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1735_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                v___x_1736_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_1733_, v___x_1731_, v___x_1735_);
                if leanh::lean_obj_tag(v___x_1736_) == 0 {
                    v_a_1737_ = leanh::lean_ctor_get(v___x_1736_, 0);
                    v_isSharedCheck_1744_ = (!leanh::lean_is_exclusive(v___x_1736_)) as u8;
                    if v_isSharedCheck_1744_ == 0 {
                        v___x_1739_ = v___x_1736_;
                        v_isShared_1740_ = v_isSharedCheck_1744_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1737_);
                        leanh::lean_dec(v___x_1736_);
                        v___x_1739_ = leanh::lean_box(0);
                        v_isShared_1740_ = v_isSharedCheck_1744_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1745_ = leanh::lean_ctor_get(v___x_1736_, 0);
                    v_isSharedCheck_1753_ = (!leanh::lean_is_exclusive(v___x_1736_)) as u8;
                    if v_isSharedCheck_1753_ == 0 {
                        v___x_1747_ = v___x_1736_;
                        v_isShared_1748_ = v_isSharedCheck_1753_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1745_);
                        leanh::lean_dec(v___x_1736_);
                        v___x_1747_ = leanh::lean_box(0);
                        v_isShared_1748_ = v_isSharedCheck_1753_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1740_ == 0 {
                    v___x_1742_ = v___x_1739_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1743_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
                    v___x_1742_ = v_reuseFailAlloc_1743_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1742_;
            }
            4 => {
                v___x_1749_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1749_, 0, v_a_1745_);
                if v_isShared_1748_ == 0 {
                    leanh::lean_ctor_set(v___x_1747_, 0, v___x_1749_);
                    v___x_1751_ = v___x_1747_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1752_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
                    v___x_1751_ = v_reuseFailAlloc_1752_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1751_;
            }
            6 => {
                v___x_1763_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1763_, 0, v_a_1756_);
                leanh::lean_ctor_set(v___x_1763_, 1, v_a_1759_);
                if v_isShared_1762_ == 0 {
                    leanh::lean_ctor_set(v___x_1761_, 0, v___x_1763_);
                    v___x_1765_ = v___x_1761_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
                    v___x_1765_ = v_reuseFailAlloc_1766_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___lam__0(
    mut v_o_1774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut v_text_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_o_1774_) == 0 {
                    v_range_1775_ = leanh::lean_ctor_get(v_o_1774_, 0);
                    v_text_1776_ = leanh::lean_ctor_get(v_o_1774_, 1);
                    v_isSharedCheck_1792_ = (!leanh::lean_is_exclusive(v_o_1774_)) as u8;
                    if v_isSharedCheck_1792_ == 0 {
                        v___x_1778_ = v_o_1774_;
                        v_isShared_1779_ = v_isSharedCheck_1792_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_text_1776_);
                        leanh::lean_inc(v_range_1775_);
                        leanh::lean_dec(v_o_1774_);
                        v___x_1778_ = leanh::lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_1792_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_text_1793_ = leanh::lean_ctor_get(v_o_1774_, 0);
                    v_isSharedCheck_1805_ = (!leanh::lean_is_exclusive(v_o_1774_)) as u8;
                    if v_isSharedCheck_1805_ == 0 {
                        v___x_1795_ = v_o_1774_;
                        v_isShared_1796_ = v_isSharedCheck_1805_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_text_1793_);
                        leanh::lean_dec(v_o_1774_);
                        v___x_1795_ = leanh::lean_box(0);
                        v_isShared_1796_ = v_isSharedCheck_1805_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1780_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1;
                v___x_1781_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1775_);
                if v_isShared_1779_ == 0 {
                    leanh::lean_ctor_set(v___x_1778_, 1, v___x_1781_);
                    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1780_);
                    v___x_1783_ = v___x_1778_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 1, v___x_1781_);
                    v___x_1783_ = v_reuseFailAlloc_1791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1784_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                v___x_1785_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1785_, 0, v_text_1776_);
                v___x_1786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1786_, 0, v___x_1784_);
                leanh::lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                v___x_1787_ = leanh::lean_box(0);
                v___x_1788_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1788_, 0, v___x_1786_);
                leanh::lean_ctor_set(v___x_1788_, 1, v___x_1787_);
                v___x_1789_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1789_, 0, v___x_1783_);
                leanh::lean_ctor_set(v___x_1789_, 1, v___x_1788_);
                v___x_1790_ = l_Lean_Json_mkObj(v___x_1789_);
                leanh::lean_dec_ref_known(v___x_1789_, 2);
                return v___x_1790_;
            }
            3 => {
                v___x_1797_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                if v_isShared_1796_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1795_, 3);
                    v___x_1799_ = v___x_1795_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_text_1793_);
                    v___x_1799_ = v_reuseFailAlloc_1804_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1800_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1800_, 0, v___x_1797_);
                leanh::lean_ctor_set(v___x_1800_, 1, v___x_1799_);
                v___x_1801_ = leanh::lean_box(0);
                v___x_1802_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1802_, 0, v___x_1800_);
                leanh::lean_ctor_set(v___x_1802_, 1, v___x_1801_);
                v___x_1803_ = l_Lean_Json_mkObj(v___x_1802_);
                leanh::lean_dec_ref_known(v___x_1802_, 2);
                return v___x_1803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(
    mut v_sz_1808_: usize,
    mut v_i_1809_: usize,
    mut v_bs_1810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1811_: u8 = 0;
    let mut v_v_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: usize = 0;
    let mut v___x_1818_: usize = 0;
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1825_: u8 = 0;
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut v_text_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1811_ = lean_usize_dec_lt(v_i_1809_, v_sz_1808_);
                if v___x_1811_ == 0 {
                    return v_bs_1810_;
                } else {
                    v_v_1812_ = lean_array_uget(v_bs_1810_, v_i_1809_);
                    v___x_1813_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1814_ = lean_array_uset(v_bs_1810_, v_i_1809_, v___x_1813_);
                    if leanh::lean_obj_tag(v_v_1812_) == 0 {
                        v_range_1821_ = leanh::lean_ctor_get(v_v_1812_, 0);
                        v_text_1822_ = leanh::lean_ctor_get(v_v_1812_, 1);
                        v_isSharedCheck_1838_ = (!leanh::lean_is_exclusive(v_v_1812_)) as u8;
                        if v_isSharedCheck_1838_ == 0 {
                            v___x_1824_ = v_v_1812_;
                            v_isShared_1825_ = v_isSharedCheck_1838_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_text_1822_);
                            leanh::lean_inc(v_range_1821_);
                            leanh::lean_dec(v_v_1812_);
                            v___x_1824_ = leanh::lean_box(0);
                            v_isShared_1825_ = v_isSharedCheck_1838_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_text_1839_ = leanh::lean_ctor_get(v_v_1812_, 0);
                        v_isSharedCheck_1851_ = (!leanh::lean_is_exclusive(v_v_1812_)) as u8;
                        if v_isSharedCheck_1851_ == 0 {
                            v___x_1841_ = v_v_1812_;
                            v_isShared_1842_ = v_isSharedCheck_1851_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_text_1839_);
                            leanh::lean_dec(v_v_1812_);
                            v___x_1841_ = leanh::lean_box(0);
                            v_isShared_1842_ = v_isSharedCheck_1851_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1817_ = 1usize;
                v___x_1818_ = lean_usize_add(v_i_1809_, v___x_1817_);
                v___x_1819_ = lean_array_uset(v_bs_x27_1814_, v_i_1809_, v___y_1816_);
                v_i_1809_ = v___x_1818_;
                v_bs_1810_ = v___x_1819_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1826_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1;
                v___x_1827_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1821_);
                if v_isShared_1825_ == 0 {
                    leanh::lean_ctor_set(v___x_1824_, 1, v___x_1827_);
                    leanh::lean_ctor_set(v___x_1824_, 0, v___x_1826_);
                    v___x_1829_ = v___x_1824_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 1, v___x_1827_);
                    v___x_1829_ = v_reuseFailAlloc_1837_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1830_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                v___x_1831_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1831_, 0, v_text_1822_);
                v___x_1832_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1832_, 0, v___x_1830_);
                leanh::lean_ctor_set(v___x_1832_, 1, v___x_1831_);
                v___x_1833_ = leanh::lean_box(0);
                v___x_1834_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1834_, 0, v___x_1832_);
                leanh::lean_ctor_set(v___x_1834_, 1, v___x_1833_);
                v___x_1835_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1835_, 0, v___x_1829_);
                leanh::lean_ctor_set(v___x_1835_, 1, v___x_1834_);
                v___x_1836_ = l_Lean_Json_mkObj(v___x_1835_);
                leanh::lean_dec_ref_known(v___x_1835_, 2);
                v___y_1816_ = v___x_1836_;
                state = 1;
                continue;
            }
            4 => {
                v___x_1843_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                if v_isShared_1842_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1841_, 3);
                    v___x_1845_ = v___x_1841_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1850_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_text_1839_);
                    v___x_1845_ = v_reuseFailAlloc_1850_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1846_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1846_, 0, v___x_1843_);
                leanh::lean_ctor_set(v___x_1846_, 1, v___x_1845_);
                v___x_1847_ = leanh::lean_box(0);
                v___x_1848_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1848_, 0, v___x_1846_);
                leanh::lean_ctor_set(v___x_1848_, 1, v___x_1847_);
                v___x_1849_ = l_Lean_Json_mkObj(v___x_1848_);
                leanh::lean_dec_ref_known(v___x_1848_, 2);
                v___y_1816_ = v___x_1849_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0___boxed(
    mut v_sz_1852_: *mut leanh::LeanObject,
    mut v_i_1853_: *mut leanh::LeanObject,
    mut v_bs_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1855_: usize = 0;
    let mut v_i_boxed_1856_: usize = 0;
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1855_ = leanh::lean_unbox_usize(v_sz_1852_);
    leanh::lean_dec(v_sz_1852_);
    v_i_boxed_1856_ = leanh::lean_unbox_usize(v_i_1853_);
    leanh::lean_dec(v_i_1853_);
    v_res_1857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_boxed_1855_, v_i_boxed_1856_, v_bs_1854_);
    return v_res_1857_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(
    mut v_a_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1859_: usize = 0;
    let mut v___x_1860_: usize = 0;
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_1859_ = lean_array_size(v_a_1858_);
    v___x_1860_ = 0usize;
    v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_1859_, v___x_1860_, v_a_1858_);
    v___x_1862_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1862_, 0, v___x_1861_);
    return v___x_1862_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson(
    mut v_x_1864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_textDocument_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contentChanges_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1869_: u8 = 0;
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_textDocument_1865_ = leanh::lean_ctor_get(v_x_1864_, 0);
                v_contentChanges_1866_ = leanh::lean_ctor_get(v_x_1864_, 1);
                v_isSharedCheck_1886_ = (!leanh::lean_is_exclusive(v_x_1864_)) as u8;
                if v_isSharedCheck_1886_ == 0 {
                    v___x_1868_ = v_x_1864_;
                    v_isShared_1869_ = v_isSharedCheck_1886_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_contentChanges_1866_);
                    leanh::lean_inc(v_textDocument_1865_);
                    leanh::lean_dec(v_x_1864_);
                    v___x_1868_ = leanh::lean_box(0);
                    v_isShared_1869_ = v_isSharedCheck_1886_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1870_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                v___x_1871_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(
                    v_textDocument_1865_,
                );
                if v_isShared_1869_ == 0 {
                    leanh::lean_ctor_set(v___x_1868_, 1, v___x_1871_);
                    leanh::lean_ctor_set(v___x_1868_, 0, v___x_1870_);
                    v___x_1873_ = v___x_1868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1885_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___x_1871_);
                    v___x_1873_ = v_reuseFailAlloc_1885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1874_ = leanh::lean_box(0);
                v___x_1875_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1875_, 0, v___x_1873_);
                leanh::lean_ctor_set(v___x_1875_, 1, v___x_1874_);
                v___x_1876_ = l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0;
                v___x_1877_ = l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(v_contentChanges_1866_);
                v___x_1878_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1878_, 0, v___x_1876_);
                leanh::lean_ctor_set(v___x_1878_, 1, v___x_1877_);
                v___x_1879_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1879_, 0, v___x_1878_);
                leanh::lean_ctor_set(v___x_1879_, 1, v___x_1874_);
                v___x_1880_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1880_, 0, v___x_1879_);
                leanh::lean_ctor_set(v___x_1880_, 1, v___x_1874_);
                v___x_1881_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1881_, 0, v___x_1875_);
                leanh::lean_ctor_set(v___x_1881_, 1, v___x_1880_);
                v___x_1882_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
                v___x_1883_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_1881_, v___x_1882_);
                v___x_1884_ = l_Lean_Json_mkObj(v___x_1883_);
                leanh::lean_dec(v___x_1883_);
                return v___x_1884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(
    mut v_j_1889_: *mut leanh::LeanObject,
    mut v_k_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_Json_getObjValD(v_j_1889_, v_k_1890_);
    v___x_1892_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0___boxed(
    mut v_j_1893_: *mut leanh::LeanObject,
    mut v_k_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_j_1893_, v_k_1894_);
    leanh::lean_dec_ref(v_k_1894_);
    return v_res_1895_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(
    mut v_j_1896_: *mut leanh::LeanObject,
    mut v_k_1897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_Json_getObjValD(v_j_1896_, v_k_1897_);
    v___x_1899_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_1898_);
    return v___x_1899_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3___boxed(
    mut v_j_1900_: *mut leanh::LeanObject,
    mut v_k_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_j_1900_, v_k_1901_);
    leanh::lean_dec_ref(v_k_1901_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(
    mut v_j_1903_: *mut leanh::LeanObject,
    mut v_k_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1905_ = l_Lean_Json_getObjValD(v_j_1903_, v_k_1904_);
    v___x_1906_ = l_Lean_Json_getStr_x3f(v___x_1905_);
    return v___x_1906_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2___boxed(
    mut v_j_1907_: *mut leanh::LeanObject,
    mut v_k_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_j_1907_, v_k_1908_);
    leanh::lean_dec_ref(v_k_1908_);
    return v_res_1909_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(
    mut v_sz_1910_: usize,
    mut v_i_1911_: usize,
    mut v_bs_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1913_: u8 = 0;
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: usize = 0;
    let mut v___x_1921_: usize = 0;
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1934_: u8 = 0;
    let mut v_a_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1913_ = lean_usize_dec_lt(v_i_1911_, v_sz_1910_);
                if v___x_1913_ == 0 {
                    v___x_1914_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1914_, 0, v_bs_1912_);
                    return v___x_1914_;
                } else {
                    v_v_1915_ = lean_array_uget(v_bs_1912_, v_i_1911_);
                    v___x_1916_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1917_ = lean_array_uset(v_bs_1912_, v_i_1911_, v___x_1916_);
                    v___x_1937_ =
                        l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1;
                    leanh::lean_inc(v_v_1915_);
                    v___x_1938_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_v_1915_, v___x_1937_);
                    if leanh::lean_obj_tag(v___x_1938_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1938_, 1);
                        state = 2;
                        continue;
                    } else {
                        v_a_1939_ = leanh::lean_ctor_get(v___x_1938_, 0);
                        leanh::lean_inc(v_a_1939_);
                        leanh::lean_dec_ref_known(v___x_1938_, 1);
                        v___x_1940_ = l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                        leanh::lean_inc(v_v_1915_);
                        v___x_1941_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_1915_, v___x_1940_);
                        if leanh::lean_obj_tag(v___x_1941_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1941_, 1);
                            leanh::lean_dec(v_a_1939_);
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v_v_1915_);
                            v_a_1942_ = leanh::lean_ctor_get(v___x_1941_, 0);
                            leanh::lean_inc(v_a_1942_);
                            leanh::lean_dec_ref_known(v___x_1941_, 1);
                            v___x_1943_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1943_, 0, v_a_1939_);
                            leanh::lean_ctor_set(v___x_1943_, 1, v_a_1942_);
                            v_a_1919_ = v___x_1943_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1920_ = 1usize;
                v___x_1921_ = lean_usize_add(v_i_1911_, v___x_1920_);
                v___x_1922_ = lean_array_uset(v_bs_x27_1917_, v_i_1911_, v_a_1919_);
                v_i_1911_ = v___x_1921_;
                v_bs_1912_ = v___x_1922_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1925_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                v___x_1926_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_1915_, v___x_1925_);
                if leanh::lean_obj_tag(v___x_1926_) == 0 {
                    leanh::lean_dec_ref(v_bs_x27_1917_);
                    v_a_1927_ = leanh::lean_ctor_get(v___x_1926_, 0);
                    v_isSharedCheck_1934_ = (!leanh::lean_is_exclusive(v___x_1926_)) as u8;
                    if v_isSharedCheck_1934_ == 0 {
                        v___x_1929_ = v___x_1926_;
                        v_isShared_1930_ = v_isSharedCheck_1934_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1927_);
                        leanh::lean_dec(v___x_1926_);
                        v___x_1929_ = leanh::lean_box(0);
                        v_isShared_1930_ = v_isSharedCheck_1934_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1935_ = leanh::lean_ctor_get(v___x_1926_, 0);
                    leanh::lean_inc(v_a_1935_);
                    leanh::lean_dec_ref_known(v___x_1926_, 1);
                    v___x_1936_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1936_, 0, v_a_1935_);
                    v_a_1919_ = v___x_1936_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_1930_ == 0 {
                    v___x_1932_ = v___x_1929_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1933_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
                    v___x_1932_ = v_reuseFailAlloc_1933_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4___boxed(
    mut v_sz_1944_: *mut leanh::LeanObject,
    mut v_i_1945_: *mut leanh::LeanObject,
    mut v_bs_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1947_: usize = 0;
    let mut v_i_boxed_1948_: usize = 0;
    let mut v_res_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1947_ = leanh::lean_unbox_usize(v_sz_1944_);
    leanh::lean_dec(v_sz_1944_);
    v_i_boxed_1948_ = leanh::lean_unbox_usize(v_i_1945_);
    leanh::lean_dec(v_i_1945_);
    v_res_1949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_boxed_1947_, v_i_boxed_1948_, v_bs_1946_);
    return v_res_1949_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(
    mut v_x_1950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1950_) == 4 {
        let mut v_elems_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1952_: usize = 0;
        let mut v___x_1953_: usize = 0;
        let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_1951_ = leanh::lean_ctor_get(v_x_1950_, 0);
        leanh::lean_inc_ref(v_elems_1951_);
        leanh::lean_dec_ref_known(v_x_1950_, 1);
        v_sz_1952_ = lean_array_size(v_elems_1951_);
        v___x_1953_ = 0usize;
        v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_1952_, v___x_1953_, v_elems_1951_);
        return v___x_1954_;
    } else {
        let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1955_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0;
        v___x_1956_ = leanh::lean_unsigned_to_nat(80);
        v___x_1957_ = l_Lean_Json_pretty(v_x_1950_, v___x_1956_);
        v___x_1958_ = lean_string_append(v___x_1955_, v___x_1957_);
        leanh::lean_dec_ref(v___x_1957_);
        v___x_1959_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1;
        v___x_1960_ = lean_string_append(v___x_1958_, v___x_1959_);
        v___x_1961_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1961_, 0, v___x_1960_);
        return v___x_1961_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(
    mut v_j_1962_: *mut leanh::LeanObject,
    mut v_k_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_Json_getObjValD(v_j_1962_, v_k_1963_);
    v___x_1965_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(v___x_1964_);
    return v___x_1965_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1___boxed(
    mut v_j_1966_: *mut leanh::LeanObject,
    mut v_k_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1968_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_j_1966_, v_k_1967_);
    leanh::lean_dec_ref(v_k_1967_);
    return v_res_1968_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1974_: u8 = 0;
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1974_ = 1;
    v___x_1975_ = l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1;
    v___x_1976_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1975_, v___x_1974_);
    return v___x_1976_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_1978_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2,
    );
    v___x_1979_ = lean_string_append(v___x_1978_, v___x_1977_);
    return v___x_1979_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1980_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8,
    );
    v___x_1981_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3,
    );
    v___x_1982_ = lean_string_append(v___x_1981_, v___x_1980_);
    return v___x_1982_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1983_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_1984_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4,
    );
    v___x_1985_ = lean_string_append(v___x_1984_, v___x_1983_);
    return v___x_1985_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1988_ = 1;
    v___x_1989_ = l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6;
    v___x_1990_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1989_, v___x_1988_);
    return v___x_1990_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7,
    );
    v___x_1992_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3,
    );
    v___x_1993_ = lean_string_append(v___x_1992_, v___x_1991_);
    return v___x_1993_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_1995_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8,
    );
    v___x_1996_ = lean_string_append(v___x_1995_, v___x_1994_);
    return v___x_1996_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson(
    mut v_json_1997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v_a_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_a_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2024_: u8 = 0;
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v_a_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_a_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1998_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                leanh::lean_inc(v_json_1997_);
                v___x_1999_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_json_1997_, v___x_1998_);
                if leanh::lean_obj_tag(v___x_1999_) == 0 {
                    leanh::lean_dec(v_json_1997_);
                    v_a_2000_ = leanh::lean_ctor_get(v___x_1999_, 0);
                    v_isSharedCheck_2009_ = (!leanh::lean_is_exclusive(v___x_1999_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_2002_ = v___x_1999_;
                        v_isShared_2003_ = v_isSharedCheck_2009_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2000_);
                        leanh::lean_dec(v___x_1999_);
                        v___x_2002_ = leanh::lean_box(0);
                        v_isShared_2003_ = v_isSharedCheck_2009_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_1999_) == 0 {
                        leanh::lean_dec(v_json_1997_);
                        v_a_2010_ = leanh::lean_ctor_get(v___x_1999_, 0);
                        v_isSharedCheck_2017_ =
                            (!leanh::lean_is_exclusive(v___x_1999_)) as u8;
                        if v_isSharedCheck_2017_ == 0 {
                            v___x_2012_ = v___x_1999_;
                            v_isShared_2013_ = v_isSharedCheck_2017_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2010_);
                            leanh::lean_dec(v___x_1999_);
                            v___x_2012_ = leanh::lean_box(0);
                            v_isShared_2013_ = v_isSharedCheck_2017_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2018_ = leanh::lean_ctor_get(v___x_1999_, 0);
                        leanh::lean_inc(v_a_2018_);
                        leanh::lean_dec_ref_known(v___x_1999_, 1);
                        v___x_2019_ =
                            l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0;
                        v___x_2020_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_json_1997_, v___x_2019_);
                        if leanh::lean_obj_tag(v___x_2020_) == 0 {
                            leanh::lean_dec(v_a_2018_);
                            v_a_2021_ = leanh::lean_ctor_get(v___x_2020_, 0);
                            v_isSharedCheck_2030_ =
                                (!leanh::lean_is_exclusive(v___x_2020_)) as u8;
                            if v_isSharedCheck_2030_ == 0 {
                                v___x_2023_ = v___x_2020_;
                                v_isShared_2024_ = v_isSharedCheck_2030_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2021_);
                                leanh::lean_dec(v___x_2020_);
                                v___x_2023_ = leanh::lean_box(0);
                                v_isShared_2024_ = v_isSharedCheck_2030_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_2020_) == 0 {
                                leanh::lean_dec(v_a_2018_);
                                v_a_2031_ = leanh::lean_ctor_get(v___x_2020_, 0);
                                v_isSharedCheck_2038_ =
                                    (!leanh::lean_is_exclusive(v___x_2020_)) as u8;
                                if v_isSharedCheck_2038_ == 0 {
                                    v___x_2033_ = v___x_2020_;
                                    v_isShared_2034_ = v_isSharedCheck_2038_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2031_);
                                    leanh::lean_dec(v___x_2020_);
                                    v___x_2033_ = leanh::lean_box(0);
                                    v_isShared_2034_ = v_isSharedCheck_2038_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2039_ = leanh::lean_ctor_get(v___x_2020_, 0);
                                v_isSharedCheck_2047_ =
                                    (!leanh::lean_is_exclusive(v___x_2020_)) as u8;
                                if v_isSharedCheck_2047_ == 0 {
                                    v___x_2041_ = v___x_2020_;
                                    v_isShared_2042_ = v_isSharedCheck_2047_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2039_);
                                    leanh::lean_dec(v___x_2020_);
                                    v___x_2041_ = leanh::lean_box(0);
                                    v_isShared_2042_ = v_isSharedCheck_2047_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2004_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5_once), _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5);
                v___x_2005_ = lean_string_append(v___x_2004_, v_a_2000_);
                leanh::lean_dec(v_a_2000_);
                if v_isShared_2003_ == 0 {
                    leanh::lean_ctor_set(v___x_2002_, 0, v___x_2005_);
                    v___x_2007_ = v___x_2002_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2007_;
            }
            3 => {
                if v_isShared_2013_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2012_, 0);
                    v___x_2015_ = v___x_2012_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
                    v___x_2015_ = v_reuseFailAlloc_2016_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2015_;
            }
            5 => {
                v___x_2025_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9_once), _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9);
                v___x_2026_ = lean_string_append(v___x_2025_, v_a_2021_);
                leanh::lean_dec(v_a_2021_);
                if v_isShared_2024_ == 0 {
                    leanh::lean_ctor_set(v___x_2023_, 0, v___x_2026_);
                    v___x_2028_ = v___x_2023_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2029_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                    v___x_2028_ = v_reuseFailAlloc_2029_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2028_;
            }
            7 => {
                if v_isShared_2034_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2033_, 0);
                    v___x_2036_ = v___x_2033_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2036_;
            }
            9 => {
                v___x_2043_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2043_, 0, v_a_2018_);
                leanh::lean_ctor_set(v___x_2043_, 1, v_a_2039_);
                if v_isShared_2042_ == 0 {
                    leanh::lean_ctor_set(v___x_2041_, 0, v___x_2043_);
                    v___x_2045_ = v___x_2041_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2046_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
                    v___x_2045_ = v_reuseFailAlloc_2046_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(
    mut v_k_2050_: *mut leanh::LeanObject,
    mut v_x_2051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2056_: u8 = 0;
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2051_) == 0 {
                    leanh::lean_dec_ref(v_k_2050_);
                    v___x_2052_ = leanh::lean_box(0);
                    return v___x_2052_;
                } else {
                    v_val_2053_ = leanh::lean_ctor_get(v_x_2051_, 0);
                    v_isSharedCheck_2063_ = (!leanh::lean_is_exclusive(v_x_2051_)) as u8;
                    if v_isSharedCheck_2063_ == 0 {
                        v___x_2055_ = v_x_2051_;
                        v_isShared_2056_ = v_isSharedCheck_2063_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2053_);
                        leanh::lean_dec(v_x_2051_);
                        v___x_2055_ = leanh::lean_box(0);
                        v_isShared_2056_ = v_isSharedCheck_2063_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2056_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2055_, 3);
                    v___x_2058_ = v___x_2055_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2062_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_val_2053_);
                    v___x_2058_ = v_reuseFailAlloc_2062_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2059_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2059_, 0, v_k_2050_);
                leanh::lean_ctor_set(v___x_2059_, 1, v___x_2058_);
                v___x_2060_ = leanh::lean_box(0);
                v___x_2061_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2061_, 0, v___x_2059_);
                leanh::lean_ctor_set(v___x_2061_, 1, v___x_2060_);
                return v___x_2061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson(
    mut v_x_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_textDocument_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_textDocument_2065_ = leanh::lean_ctor_get(v_x_2064_, 0);
                v_text_x3f_2066_ = leanh::lean_ctor_get(v_x_2064_, 1);
                v_isSharedCheck_2084_ = (!leanh::lean_is_exclusive(v_x_2064_)) as u8;
                if v_isSharedCheck_2084_ == 0 {
                    v___x_2068_ = v_x_2064_;
                    v_isShared_2069_ = v_isSharedCheck_2084_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_text_x3f_2066_);
                    leanh::lean_inc(v_textDocument_2065_);
                    leanh::lean_dec(v_x_2064_);
                    v___x_2068_ = leanh::lean_box(0);
                    v_isShared_2069_ = v_isSharedCheck_2084_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2070_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                v___x_2071_ =
                    l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_2065_);
                if v_isShared_2069_ == 0 {
                    leanh::lean_ctor_set(v___x_2068_, 1, v___x_2071_);
                    leanh::lean_ctor_set(v___x_2068_, 0, v___x_2070_);
                    v___x_2073_ = v___x_2068_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2070_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2071_);
                    v___x_2073_ = v_reuseFailAlloc_2083_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2074_ = leanh::lean_box(0);
                v___x_2075_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2075_, 0, v___x_2073_);
                leanh::lean_ctor_set(v___x_2075_, 1, v___x_2074_);
                v___x_2076_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                v___x_2077_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(v___x_2076_, v_text_x3f_2066_);
                v___x_2078_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2078_, 0, v___x_2077_);
                leanh::lean_ctor_set(v___x_2078_, 1, v___x_2074_);
                v___x_2079_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2079_, 0, v___x_2075_);
                leanh::lean_ctor_set(v___x_2079_, 1, v___x_2078_);
                v___x_2080_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
                v___x_2081_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_2079_, v___x_2080_);
                v___x_2082_ = l_Lean_Json_mkObj(v___x_2081_);
                leanh::lean_dec(v___x_2081_);
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(
    mut v_j_2087_: *mut leanh::LeanObject,
    mut v_k_2088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = l_Lean_Json_getObjValD(v_j_2087_, v_k_2088_);
    v___x_2090_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_2089_);
    return v___x_2090_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0___boxed(
    mut v_j_2091_: *mut leanh::LeanObject,
    mut v_k_2092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2093_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_j_2091_, v_k_2092_);
    leanh::lean_dec_ref(v_k_2092_);
    return v_res_2093_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(
    mut v_x_2096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2102_: u8 = 0;
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2106_: u8 = 0;
    let mut v_a_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2115_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2096_) == 0 {
                    v___x_2097_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0;
                    return v___x_2097_;
                } else {
                    v___x_2098_ = l_Lean_Json_getStr_x3f(v_x_2096_);
                    if leanh::lean_obj_tag(v___x_2098_) == 0 {
                        v_a_2099_ = leanh::lean_ctor_get(v___x_2098_, 0);
                        v_isSharedCheck_2106_ =
                            (!leanh::lean_is_exclusive(v___x_2098_)) as u8;
                        if v_isSharedCheck_2106_ == 0 {
                            v___x_2101_ = v___x_2098_;
                            v_isShared_2102_ = v_isSharedCheck_2106_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2099_);
                            leanh::lean_dec(v___x_2098_);
                            v___x_2101_ = leanh::lean_box(0);
                            v_isShared_2102_ = v_isSharedCheck_2106_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2107_ = leanh::lean_ctor_get(v___x_2098_, 0);
                        v_isSharedCheck_2115_ =
                            (!leanh::lean_is_exclusive(v___x_2098_)) as u8;
                        if v_isSharedCheck_2115_ == 0 {
                            v___x_2109_ = v___x_2098_;
                            v_isShared_2110_ = v_isSharedCheck_2115_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2107_);
                            leanh::lean_dec(v___x_2098_);
                            v___x_2109_ = leanh::lean_box(0);
                            v_isShared_2110_ = v_isSharedCheck_2115_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2102_ == 0 {
                    v___x_2104_ = v___x_2101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2105_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
                    v___x_2104_ = v_reuseFailAlloc_2105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2104_;
            }
            3 => {
                v___x_2111_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2111_, 0, v_a_2107_);
                if v_isShared_2110_ == 0 {
                    leanh::lean_ctor_set(v___x_2109_, 0, v___x_2111_);
                    v___x_2113_ = v___x_2109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2114_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
                    v___x_2113_ = v_reuseFailAlloc_2114_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(
    mut v_j_2116_: *mut leanh::LeanObject,
    mut v_k_2117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Lean_Json_getObjValD(v_j_2116_, v_k_2117_);
    v___x_2119_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(v___x_2118_);
    return v___x_2119_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1___boxed(
    mut v_j_2120_: *mut leanh::LeanObject,
    mut v_k_2121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_j_2120_, v_k_2121_);
    leanh::lean_dec_ref(v_k_2121_);
    return v_res_2122_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2128_ = 1;
    v___x_2129_ = l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1;
    v___x_2130_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2129_, v___x_2128_);
    return v___x_2130_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2131_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_2132_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2,
    );
    v___x_2133_ = lean_string_append(v___x_2132_, v___x_2131_);
    return v___x_2133_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2134_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8,
    );
    v___x_2135_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3,
    );
    v___x_2136_ = lean_string_append(v___x_2135_, v___x_2134_);
    return v___x_2136_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2138_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4,
    );
    v___x_2139_ = lean_string_append(v___x_2138_, v___x_2137_);
    return v___x_2139_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2143_: u8 = 0;
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = 1;
    v___x_2144_ = l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7;
    v___x_2145_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2144_, v___x_2143_);
    return v___x_2145_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8,
    );
    v___x_2147_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3,
    );
    v___x_2148_ = lean_string_append(v___x_2147_, v___x_2146_);
    return v___x_2148_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2149_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2150_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9,
    );
    v___x_2151_ = lean_string_append(v___x_2150_, v___x_2149_);
    return v___x_2151_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson(
    mut v_json_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut v_a_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2172_: u8 = 0;
    let mut v_a_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v_a_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2193_: u8 = 0;
    let mut v_a_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2197_: u8 = 0;
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2153_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                leanh::lean_inc(v_json_2152_);
                v___x_2154_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_2152_, v___x_2153_);
                if leanh::lean_obj_tag(v___x_2154_) == 0 {
                    leanh::lean_dec(v_json_2152_);
                    v_a_2155_ = leanh::lean_ctor_get(v___x_2154_, 0);
                    v_isSharedCheck_2164_ = (!leanh::lean_is_exclusive(v___x_2154_)) as u8;
                    if v_isSharedCheck_2164_ == 0 {
                        v___x_2157_ = v___x_2154_;
                        v_isShared_2158_ = v_isSharedCheck_2164_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2155_);
                        leanh::lean_dec(v___x_2154_);
                        v___x_2157_ = leanh::lean_box(0);
                        v_isShared_2158_ = v_isSharedCheck_2164_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_2154_) == 0 {
                        leanh::lean_dec(v_json_2152_);
                        v_a_2165_ = leanh::lean_ctor_get(v___x_2154_, 0);
                        v_isSharedCheck_2172_ =
                            (!leanh::lean_is_exclusive(v___x_2154_)) as u8;
                        if v_isSharedCheck_2172_ == 0 {
                            v___x_2167_ = v___x_2154_;
                            v_isShared_2168_ = v_isSharedCheck_2172_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2165_);
                            leanh::lean_dec(v___x_2154_);
                            v___x_2167_ = leanh::lean_box(0);
                            v_isShared_2168_ = v_isSharedCheck_2172_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2173_ = leanh::lean_ctor_get(v___x_2154_, 0);
                        leanh::lean_inc(v_a_2173_);
                        leanh::lean_dec_ref_known(v___x_2154_, 1);
                        v___x_2174_ = l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                        v___x_2175_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_json_2152_, v___x_2174_);
                        if leanh::lean_obj_tag(v___x_2175_) == 0 {
                            leanh::lean_dec(v_a_2173_);
                            v_a_2176_ = leanh::lean_ctor_get(v___x_2175_, 0);
                            v_isSharedCheck_2185_ =
                                (!leanh::lean_is_exclusive(v___x_2175_)) as u8;
                            if v_isSharedCheck_2185_ == 0 {
                                v___x_2178_ = v___x_2175_;
                                v_isShared_2179_ = v_isSharedCheck_2185_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2176_);
                                leanh::lean_dec(v___x_2175_);
                                v___x_2178_ = leanh::lean_box(0);
                                v_isShared_2179_ = v_isSharedCheck_2185_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_2175_) == 0 {
                                leanh::lean_dec(v_a_2173_);
                                v_a_2186_ = leanh::lean_ctor_get(v___x_2175_, 0);
                                v_isSharedCheck_2193_ =
                                    (!leanh::lean_is_exclusive(v___x_2175_)) as u8;
                                if v_isSharedCheck_2193_ == 0 {
                                    v___x_2188_ = v___x_2175_;
                                    v_isShared_2189_ = v_isSharedCheck_2193_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2186_);
                                    leanh::lean_dec(v___x_2175_);
                                    v___x_2188_ = leanh::lean_box(0);
                                    v_isShared_2189_ = v_isSharedCheck_2193_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2194_ = leanh::lean_ctor_get(v___x_2175_, 0);
                                v_isSharedCheck_2202_ =
                                    (!leanh::lean_is_exclusive(v___x_2175_)) as u8;
                                if v_isSharedCheck_2202_ == 0 {
                                    v___x_2196_ = v___x_2175_;
                                    v_isShared_2197_ = v_isSharedCheck_2202_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2194_);
                                    leanh::lean_dec(v___x_2175_);
                                    v___x_2196_ = leanh::lean_box(0);
                                    v_isShared_2197_ = v_isSharedCheck_2202_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2159_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5,
                );
                v___x_2160_ = lean_string_append(v___x_2159_, v_a_2155_);
                leanh::lean_dec(v_a_2155_);
                if v_isShared_2158_ == 0 {
                    leanh::lean_ctor_set(v___x_2157_, 0, v___x_2160_);
                    v___x_2162_ = v___x_2157_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
                    v___x_2162_ = v_reuseFailAlloc_2163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2162_;
            }
            3 => {
                if v_isShared_2168_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2167_, 0);
                    v___x_2170_ = v___x_2167_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
                    v___x_2170_ = v_reuseFailAlloc_2171_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2170_;
            }
            5 => {
                v___x_2180_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10,
                );
                v___x_2181_ = lean_string_append(v___x_2180_, v_a_2176_);
                leanh::lean_dec(v_a_2176_);
                if v_isShared_2179_ == 0 {
                    leanh::lean_ctor_set(v___x_2178_, 0, v___x_2181_);
                    v___x_2183_ = v___x_2178_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
                    v___x_2183_ = v_reuseFailAlloc_2184_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2183_;
            }
            7 => {
                if v_isShared_2189_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2188_, 0);
                    v___x_2191_ = v___x_2188_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2192_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
                    v___x_2191_ = v_reuseFailAlloc_2192_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2191_;
            }
            9 => {
                v___x_2198_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2198_, 0, v_a_2173_);
                leanh::lean_ctor_set(v___x_2198_, 1, v_a_2194_);
                if v_isShared_2197_ == 0 {
                    leanh::lean_ctor_set(v___x_2196_, 0, v___x_2198_);
                    v___x_2200_ = v___x_2196_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2201_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
                    v___x_2200_ = v_reuseFailAlloc_2201_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonSaveOptions_toJson(
    mut v_x_2206_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2207_ = l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0;
    v___x_2208_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
    leanh::lean_ctor_set_uint8(v___x_2208_, 0 as u32, v_x_2206_);
    v___x_2209_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2209_, 0, v___x_2207_);
    leanh::lean_ctor_set(v___x_2209_, 1, v___x_2208_);
    v___x_2210_ = leanh::lean_box(0);
    v___x_2211_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2211_, 0, v___x_2209_);
    leanh::lean_ctor_set(v___x_2211_, 1, v___x_2210_);
    v___x_2212_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2212_, 0, v___x_2211_);
    leanh::lean_ctor_set(v___x_2212_, 1, v___x_2210_);
    v___x_2213_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
    v___x_2214_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_2212_, v___x_2213_);
    v___x_2215_ = l_Lean_Json_mkObj(v___x_2214_);
    leanh::lean_dec(v___x_2214_);
    return v___x_2215_;
}
pub unsafe fn l_Lean_Lsp_instToJsonSaveOptions_toJson___boxed(
    mut v_x_2216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_29__boxed_2217_: u8 = 0;
    let mut v_res_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_29__boxed_2217_ = (leanh::lean_unbox(v_x_2216_) as u8);
    v_res_2218_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v_x_29__boxed_2217_);
    return v_res_2218_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(
    mut v_j_2221_: *mut leanh::LeanObject,
    mut v_k_2222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2223_ = l_Lean_Json_getObjValD(v_j_2221_, v_k_2222_);
    v___x_2224_ = l_Lean_Json_getBool_x3f(v___x_2223_);
    leanh::lean_dec(v___x_2223_);
    return v___x_2224_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0___boxed(
    mut v_j_2225_: *mut leanh::LeanObject,
    mut v_k_2226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2227_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(
            v_j_2225_, v_k_2226_,
        );
    leanh::lean_dec_ref(v_k_2226_);
    return v_res_2227_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2233_: u8 = 0;
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2233_ = 1;
    v___x_2234_ = l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1;
    v___x_2235_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2234_, v___x_2233_);
    return v___x_2235_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2236_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_2237_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2,
    );
    v___x_2238_ = lean_string_append(v___x_2237_, v___x_2236_);
    return v___x_2238_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2241_ = 1;
    v___x_2242_ = l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4;
    v___x_2243_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2242_, v___x_2241_);
    return v___x_2243_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2244_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5_once),
        _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5,
    );
    v___x_2245_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3,
    );
    v___x_2246_ = lean_string_append(v___x_2245_, v___x_2244_);
    return v___x_2246_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2247_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2248_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6,
    );
    v___x_2249_ = lean_string_append(v___x_2248_, v___x_2247_);
    return v___x_2249_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonSaveOptions_fromJson(
    mut v_json_2250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2256_: u8 = 0;
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v_a_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v_a_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2251_ = l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0;
                v___x_2252_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_2250_, v___x_2251_);
                if leanh::lean_obj_tag(v___x_2252_) == 0 {
                    v_a_2253_ = leanh::lean_ctor_get(v___x_2252_, 0);
                    v_isSharedCheck_2262_ = (!leanh::lean_is_exclusive(v___x_2252_)) as u8;
                    if v_isSharedCheck_2262_ == 0 {
                        v___x_2255_ = v___x_2252_;
                        v_isShared_2256_ = v_isSharedCheck_2262_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2253_);
                        leanh::lean_dec(v___x_2252_);
                        v___x_2255_ = leanh::lean_box(0);
                        v_isShared_2256_ = v_isSharedCheck_2262_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_2252_) == 0 {
                        v_a_2263_ = leanh::lean_ctor_get(v___x_2252_, 0);
                        v_isSharedCheck_2270_ =
                            (!leanh::lean_is_exclusive(v___x_2252_)) as u8;
                        if v_isSharedCheck_2270_ == 0 {
                            v___x_2265_ = v___x_2252_;
                            v_isShared_2266_ = v_isSharedCheck_2270_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2263_);
                            leanh::lean_dec(v___x_2252_);
                            v___x_2265_ = leanh::lean_box(0);
                            v_isShared_2266_ = v_isSharedCheck_2270_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2271_ = leanh::lean_ctor_get(v___x_2252_, 0);
                        v_isSharedCheck_2278_ =
                            (!leanh::lean_is_exclusive(v___x_2252_)) as u8;
                        if v_isSharedCheck_2278_ == 0 {
                            v___x_2273_ = v___x_2252_;
                            v_isShared_2274_ = v_isSharedCheck_2278_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2271_);
                            leanh::lean_dec(v___x_2252_);
                            v___x_2273_ = leanh::lean_box(0);
                            v_isShared_2274_ = v_isSharedCheck_2278_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2257_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7,
                );
                v___x_2258_ = lean_string_append(v___x_2257_, v_a_2253_);
                leanh::lean_dec(v_a_2253_);
                if v_isShared_2256_ == 0 {
                    leanh::lean_ctor_set(v___x_2255_, 0, v___x_2258_);
                    v___x_2260_ = v___x_2255_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
                    v___x_2260_ = v_reuseFailAlloc_2261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2260_;
            }
            3 => {
                if v_isShared_2266_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2265_, 0);
                    v___x_2268_ = v___x_2265_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2268_;
            }
            5 => {
                if v_isShared_2274_ == 0 {
                    v___x_2276_ = v___x_2273_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2277_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDidCloseTextDocumentParams_toJson(
    mut v_x_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2282_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
    v___x_2283_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_2281_);
    v___x_2284_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2284_, 0, v___x_2282_);
    leanh::lean_ctor_set(v___x_2284_, 1, v___x_2283_);
    v___x_2285_ = leanh::lean_box(0);
    v___x_2286_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2286_, 0, v___x_2284_);
    leanh::lean_ctor_set(v___x_2286_, 1, v___x_2285_);
    v___x_2287_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2287_, 0, v___x_2286_);
    leanh::lean_ctor_set(v___x_2287_, 1, v___x_2285_);
    v___x_2288_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
    v___x_2289_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_2287_, v___x_2288_);
    v___x_2290_ = l_Lean_Json_mkObj(v___x_2289_);
    leanh::lean_dec(v___x_2289_);
    return v___x_2290_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2298_ = 1;
    v___x_2299_ = l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1;
    v___x_2300_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2299_, v___x_2298_);
    return v___x_2300_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2301_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_2302_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2,
    );
    v___x_2303_ = lean_string_append(v___x_2302_, v___x_2301_);
    return v___x_2303_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2304_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8,
    );
    v___x_2305_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3,
    );
    v___x_2306_ = lean_string_append(v___x_2305_, v___x_2304_);
    return v___x_2306_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2307_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2308_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4,
    );
    v___x_2309_ = lean_string_append(v___x_2308_, v___x_2307_);
    return v___x_2309_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson(
    mut v_json_2310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2316_: u8 = 0;
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_a_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2326_: u8 = 0;
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_a_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2311_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                v___x_2312_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_2310_, v___x_2311_);
                if leanh::lean_obj_tag(v___x_2312_) == 0 {
                    v_a_2313_ = leanh::lean_ctor_get(v___x_2312_, 0);
                    v_isSharedCheck_2322_ = (!leanh::lean_is_exclusive(v___x_2312_)) as u8;
                    if v_isSharedCheck_2322_ == 0 {
                        v___x_2315_ = v___x_2312_;
                        v_isShared_2316_ = v_isSharedCheck_2322_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2313_);
                        leanh::lean_dec(v___x_2312_);
                        v___x_2315_ = leanh::lean_box(0);
                        v_isShared_2316_ = v_isSharedCheck_2322_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_2312_) == 0 {
                        v_a_2323_ = leanh::lean_ctor_get(v___x_2312_, 0);
                        v_isSharedCheck_2330_ =
                            (!leanh::lean_is_exclusive(v___x_2312_)) as u8;
                        if v_isSharedCheck_2330_ == 0 {
                            v___x_2325_ = v___x_2312_;
                            v_isShared_2326_ = v_isSharedCheck_2330_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2323_);
                            leanh::lean_dec(v___x_2312_);
                            v___x_2325_ = leanh::lean_box(0);
                            v_isShared_2326_ = v_isSharedCheck_2330_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2331_ = leanh::lean_ctor_get(v___x_2312_, 0);
                        v_isSharedCheck_2338_ =
                            (!leanh::lean_is_exclusive(v___x_2312_)) as u8;
                        if v_isSharedCheck_2338_ == 0 {
                            v___x_2333_ = v___x_2312_;
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2331_);
                            leanh::lean_dec(v___x_2312_);
                            v___x_2333_ = leanh::lean_box(0);
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2317_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5,
                );
                v___x_2318_ = lean_string_append(v___x_2317_, v_a_2313_);
                leanh::lean_dec(v_a_2313_);
                if v_isShared_2316_ == 0 {
                    leanh::lean_ctor_set(v___x_2315_, 0, v___x_2318_);
                    v___x_2320_ = v___x_2315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
                    v___x_2320_ = v_reuseFailAlloc_2321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2320_;
            }
            3 => {
                if v_isShared_2326_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2325_, 0);
                    v___x_2328_ = v___x_2325_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
                    v___x_2328_ = v_reuseFailAlloc_2329_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2328_;
            }
            5 => {
                if v_isShared_2334_ == 0 {
                    v___x_2336_ = v___x_2333_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
                    v___x_2336_ = v_reuseFailAlloc_2337_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(
    mut v_k_2341_: *mut leanh::LeanObject,
    mut v_x_2342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2342_) == 0 {
        let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_2341_);
        v___x_2343_ = leanh::lean_box(0);
        return v___x_2343_;
    } else {
        let mut v_val_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2345_: u8 = 0;
        let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2344_ = leanh::lean_ctor_get(v_x_2342_, 0);
        v___x_2345_ = (leanh::lean_unbox(v_val_2344_) as u8);
        v___x_2346_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v___x_2345_);
        v___x_2347_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2347_, 0, v_k_2341_);
        leanh::lean_ctor_set(v___x_2347_, 1, v___x_2346_);
        v___x_2348_ = leanh::lean_box(0);
        v___x_2349_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2349_, 0, v___x_2347_);
        leanh::lean_ctor_set(v___x_2349_, 1, v___x_2348_);
        return v___x_2349_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0___boxed(
    mut v_k_2350_: *mut leanh::LeanObject,
    mut v_x_2351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2352_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(
            v_k_2350_, v_x_2351_,
        );
    leanh::lean_dec(v_x_2351_);
    return v_res_2352_;
}
pub unsafe fn l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(
    mut v_x_2358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_openClose_2359_: u8 = 0;
    let mut v_change_2360_: u8 = 0;
    let mut v_willSave_2361_: u8 = 0;
    let mut v_willSaveWaitUntil_2362_: u8 = 0;
    let mut v_save_x3f_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_openClose_2359_ = leanh::lean_ctor_get_uint8(
                    v_x_2358_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_change_2360_ = leanh::lean_ctor_get_uint8(
                    v_x_2358_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_willSave_2361_ = leanh::lean_ctor_get_uint8(
                    v_x_2358_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_willSaveWaitUntil_2362_ = leanh::lean_ctor_get_uint8(
                    v_x_2358_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 3) as u32,
                );
                v_save_x3f_2363_ = leanh::lean_ctor_get(v_x_2358_, 0);
                v___x_2364_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0;
                v___x_2365_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_2365_, 0 as u32, v_openClose_2359_);
                v___x_2366_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2366_, 0, v___x_2364_);
                leanh::lean_ctor_set(v___x_2366_, 1, v___x_2365_);
                v___x_2367_ = leanh::lean_box(0);
                v___x_2368_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2368_, 0, v___x_2366_);
                leanh::lean_ctor_set(v___x_2368_, 1, v___x_2367_);
                v___x_2369_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1;
                match v_change_2360_ {
                    0 => {
                        v___x_2392_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1,
                        );
                        v___y_2371_ = v___x_2392_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_2393_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3,
                        );
                        v___y_2371_ = v___x_2393_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2394_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once
                            ),
                            _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5,
                        );
                        v___y_2371_ = v___x_2394_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_2371_);
                v___x_2372_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2372_, 0, v___x_2369_);
                leanh::lean_ctor_set(v___x_2372_, 1, v___y_2371_);
                v___x_2373_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2373_, 0, v___x_2372_);
                leanh::lean_ctor_set(v___x_2373_, 1, v___x_2367_);
                v___x_2374_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2;
                v___x_2375_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_2375_, 0 as u32, v_willSave_2361_);
                v___x_2376_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2376_, 0, v___x_2374_);
                leanh::lean_ctor_set(v___x_2376_, 1, v___x_2375_);
                v___x_2377_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2377_, 0, v___x_2376_);
                leanh::lean_ctor_set(v___x_2377_, 1, v___x_2367_);
                v___x_2378_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3;
                v___x_2379_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_2379_, 0 as u32, v_willSaveWaitUntil_2362_);
                v___x_2380_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2380_, 0, v___x_2378_);
                leanh::lean_ctor_set(v___x_2380_, 1, v___x_2379_);
                v___x_2381_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2381_, 0, v___x_2380_);
                leanh::lean_ctor_set(v___x_2381_, 1, v___x_2367_);
                v___x_2382_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4;
                v___x_2383_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(v___x_2382_, v_save_x3f_2363_);
                v___x_2384_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2384_, 0, v___x_2383_);
                leanh::lean_ctor_set(v___x_2384_, 1, v___x_2367_);
                v___x_2385_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2385_, 0, v___x_2381_);
                leanh::lean_ctor_set(v___x_2385_, 1, v___x_2384_);
                v___x_2386_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2386_, 0, v___x_2377_);
                leanh::lean_ctor_set(v___x_2386_, 1, v___x_2385_);
                v___x_2387_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2387_, 0, v___x_2373_);
                leanh::lean_ctor_set(v___x_2387_, 1, v___x_2386_);
                v___x_2388_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2388_, 0, v___x_2368_);
                leanh::lean_ctor_set(v___x_2388_, 1, v___x_2387_);
                v___x_2389_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
                v___x_2390_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_2388_, v___x_2389_);
                v___x_2391_ = l_Lean_Json_mkObj(v___x_2390_);
                leanh::lean_dec(v___x_2390_);
                return v___x_2391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___boxed(
    mut v_x_2395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2396_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(v_x_2395_);
    leanh::lean_dec_ref(v_x_2395_);
    return v_res_2396_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(
    mut v_x_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2411_: u8 = 0;
    let mut v_a_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2415_: u8 = 0;
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2401_) == 0 {
                    v___x_2402_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0;
                    return v___x_2402_;
                } else {
                    v___x_2403_ = l_Lean_Lsp_instFromJsonSaveOptions_fromJson(v_x_2401_);
                    if leanh::lean_obj_tag(v___x_2403_) == 0 {
                        v_a_2404_ = leanh::lean_ctor_get(v___x_2403_, 0);
                        v_isSharedCheck_2411_ =
                            (!leanh::lean_is_exclusive(v___x_2403_)) as u8;
                        if v_isSharedCheck_2411_ == 0 {
                            v___x_2406_ = v___x_2403_;
                            v_isShared_2407_ = v_isSharedCheck_2411_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2404_);
                            leanh::lean_dec(v___x_2403_);
                            v___x_2406_ = leanh::lean_box(0);
                            v_isShared_2407_ = v_isSharedCheck_2411_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2412_ = leanh::lean_ctor_get(v___x_2403_, 0);
                        v_isSharedCheck_2420_ =
                            (!leanh::lean_is_exclusive(v___x_2403_)) as u8;
                        if v_isSharedCheck_2420_ == 0 {
                            v___x_2414_ = v___x_2403_;
                            v_isShared_2415_ = v_isSharedCheck_2420_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2412_);
                            leanh::lean_dec(v___x_2403_);
                            v___x_2414_ = leanh::lean_box(0);
                            v_isShared_2415_ = v_isSharedCheck_2420_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2407_ == 0 {
                    v___x_2409_ = v___x_2406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2410_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
                    v___x_2409_ = v_reuseFailAlloc_2410_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2409_;
            }
            3 => {
                v___x_2416_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2416_, 0, v_a_2412_);
                if v_isShared_2415_ == 0 {
                    leanh::lean_ctor_set(v___x_2414_, 0, v___x_2416_);
                    v___x_2418_ = v___x_2414_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2419_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
                    v___x_2418_ = v_reuseFailAlloc_2419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(
    mut v_j_2421_: *mut leanh::LeanObject,
    mut v_k_2422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2423_ = l_Lean_Json_getObjValD(v_j_2421_, v_k_2422_);
    v___x_2424_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(v___x_2423_);
    return v___x_2424_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0___boxed(
    mut v_j_2425_: *mut leanh::LeanObject,
    mut v_k_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2427_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_j_2425_, v_k_2426_);
    leanh::lean_dec_ref(v_k_2426_);
    return v_res_2427_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2433_: u8 = 0;
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2433_ = 1;
    v___x_2434_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1;
    v___x_2435_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2434_, v___x_2433_);
    return v___x_2435_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2436_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_2437_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2,
    );
    v___x_2438_ = lean_string_append(v___x_2437_, v___x_2436_);
    return v___x_2438_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2441_ = 1;
    v___x_2442_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4;
    v___x_2443_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2442_, v___x_2441_);
    return v___x_2443_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2444_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5,
    );
    v___x_2445_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3,
    );
    v___x_2446_ = lean_string_append(v___x_2445_, v___x_2444_);
    return v___x_2446_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2447_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2448_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6,
    );
    v___x_2449_ = lean_string_append(v___x_2448_, v___x_2447_);
    return v___x_2449_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2452_: u8 = 0;
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2452_ = 1;
    v___x_2453_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8;
    v___x_2454_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2453_, v___x_2452_);
    return v___x_2454_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9,
    );
    v___x_2456_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3,
    );
    v___x_2457_ = lean_string_append(v___x_2456_, v___x_2455_);
    return v___x_2457_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2458_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2459_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10,
    );
    v___x_2460_ = lean_string_append(v___x_2459_, v___x_2458_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = 1;
    v___x_2464_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12;
    v___x_2465_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2464_, v___x_2463_);
    return v___x_2465_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13,
    );
    v___x_2467_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3,
    );
    v___x_2468_ = lean_string_append(v___x_2467_, v___x_2466_);
    return v___x_2468_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2469_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2470_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14,
    );
    v___x_2471_ = lean_string_append(v___x_2470_, v___x_2469_);
    return v___x_2471_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2474_: u8 = 0;
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = 1;
    v___x_2475_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16;
    v___x_2476_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2475_, v___x_2474_);
    return v___x_2476_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17,
    );
    v___x_2478_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3,
    );
    v___x_2479_ = lean_string_append(v___x_2478_, v___x_2477_);
    return v___x_2479_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2480_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2481_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18,
    );
    v___x_2482_ = lean_string_append(v___x_2481_, v___x_2480_);
    return v___x_2482_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_2486_: u8 = 0;
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = 1;
    v___x_2487_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21;
    v___x_2488_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2487_, v___x_2486_);
    return v___x_2488_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22,
    );
    v___x_2490_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3,
    );
    v___x_2491_ = lean_string_append(v___x_2490_, v___x_2489_);
    return v___x_2491_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2493_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23,
    );
    v___x_2494_ = lean_string_append(v___x_2493_, v___x_2492_);
    return v___x_2494_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(
    mut v_json_2495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2501_: u8 = 0;
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut v_a_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2515_: u8 = 0;
    let mut v_a_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2528_: u8 = 0;
    let mut v_a_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2536_: u8 = 0;
    let mut v_a_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2543_: u8 = 0;
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2549_: u8 = 0;
    let mut v_a_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut v_a_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut v_a_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2574_: u8 = 0;
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_a_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut v_a_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2599_: u8 = 0;
    let mut v_a_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2603_: u8 = 0;
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: u8 = 0;
    let mut v___x_2606_: u8 = 0;
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: u8 = 0;
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2496_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0;
                leanh::lean_inc(v_json_2495_);
                v___x_2497_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_2495_, v___x_2496_);
                if leanh::lean_obj_tag(v___x_2497_) == 0 {
                    leanh::lean_dec(v_json_2495_);
                    v_a_2498_ = leanh::lean_ctor_get(v___x_2497_, 0);
                    v_isSharedCheck_2507_ = (!leanh::lean_is_exclusive(v___x_2497_)) as u8;
                    if v_isSharedCheck_2507_ == 0 {
                        v___x_2500_ = v___x_2497_;
                        v_isShared_2501_ = v_isSharedCheck_2507_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2498_);
                        leanh::lean_dec(v___x_2497_);
                        v___x_2500_ = leanh::lean_box(0);
                        v_isShared_2501_ = v_isSharedCheck_2507_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_2497_) == 0 {
                        leanh::lean_dec(v_json_2495_);
                        v_a_2508_ = leanh::lean_ctor_get(v___x_2497_, 0);
                        v_isSharedCheck_2515_ =
                            (!leanh::lean_is_exclusive(v___x_2497_)) as u8;
                        if v_isSharedCheck_2515_ == 0 {
                            v___x_2510_ = v___x_2497_;
                            v_isShared_2511_ = v_isSharedCheck_2515_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2508_);
                            leanh::lean_dec(v___x_2497_);
                            v___x_2510_ = leanh::lean_box(0);
                            v_isShared_2511_ = v_isSharedCheck_2515_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2516_ = leanh::lean_ctor_get(v___x_2497_, 0);
                        leanh::lean_inc(v_a_2516_);
                        leanh::lean_dec_ref_known(v___x_2497_, 1);
                        v___x_2517_ =
                            l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1;
                        leanh::lean_inc(v_json_2495_);
                        v___x_2518_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_2495_, v___x_2517_);
                        if leanh::lean_obj_tag(v___x_2518_) == 0 {
                            leanh::lean_dec(v_a_2516_);
                            leanh::lean_dec(v_json_2495_);
                            v_a_2519_ = leanh::lean_ctor_get(v___x_2518_, 0);
                            v_isSharedCheck_2528_ =
                                (!leanh::lean_is_exclusive(v___x_2518_)) as u8;
                            if v_isSharedCheck_2528_ == 0 {
                                v___x_2521_ = v___x_2518_;
                                v_isShared_2522_ = v_isSharedCheck_2528_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2519_);
                                leanh::lean_dec(v___x_2518_);
                                v___x_2521_ = leanh::lean_box(0);
                                v_isShared_2522_ = v_isSharedCheck_2528_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_2518_) == 0 {
                                leanh::lean_dec(v_a_2516_);
                                leanh::lean_dec(v_json_2495_);
                                v_a_2529_ = leanh::lean_ctor_get(v___x_2518_, 0);
                                v_isSharedCheck_2536_ =
                                    (!leanh::lean_is_exclusive(v___x_2518_)) as u8;
                                if v_isSharedCheck_2536_ == 0 {
                                    v___x_2531_ = v___x_2518_;
                                    v_isShared_2532_ = v_isSharedCheck_2536_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2529_);
                                    leanh::lean_dec(v___x_2518_);
                                    v___x_2531_ = leanh::lean_box(0);
                                    v_isShared_2532_ = v_isSharedCheck_2536_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2537_ = leanh::lean_ctor_get(v___x_2518_, 0);
                                leanh::lean_inc(v_a_2537_);
                                leanh::lean_dec_ref_known(v___x_2518_, 1);
                                v___x_2538_ =
                                    l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2;
                                leanh::lean_inc(v_json_2495_);
                                v___x_2539_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_2495_, v___x_2538_);
                                if leanh::lean_obj_tag(v___x_2539_) == 0 {
                                    leanh::lean_dec(v_a_2537_);
                                    leanh::lean_dec(v_a_2516_);
                                    leanh::lean_dec(v_json_2495_);
                                    v_a_2540_ = leanh::lean_ctor_get(v___x_2539_, 0);
                                    v_isSharedCheck_2549_ =
                                        (!leanh::lean_is_exclusive(v___x_2539_)) as u8;
                                    if v_isSharedCheck_2549_ == 0 {
                                        v___x_2542_ = v___x_2539_;
                                        v_isShared_2543_ = v_isSharedCheck_2549_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2540_);
                                        leanh::lean_dec(v___x_2539_);
                                        v___x_2542_ = leanh::lean_box(0);
                                        v_isShared_2543_ = v_isSharedCheck_2549_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_2539_) == 0 {
                                        leanh::lean_dec(v_a_2537_);
                                        leanh::lean_dec(v_a_2516_);
                                        leanh::lean_dec(v_json_2495_);
                                        v_a_2550_ = leanh::lean_ctor_get(v___x_2539_, 0);
                                        v_isSharedCheck_2557_ =
                                            (!leanh::lean_is_exclusive(v___x_2539_)) as u8;
                                        if v_isSharedCheck_2557_ == 0 {
                                            v___x_2552_ = v___x_2539_;
                                            v_isShared_2553_ = v_isSharedCheck_2557_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2550_);
                                            leanh::lean_dec(v___x_2539_);
                                            v___x_2552_ = leanh::lean_box(0);
                                            v_isShared_2553_ = v_isSharedCheck_2557_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_2558_ = leanh::lean_ctor_get(v___x_2539_, 0);
                                        leanh::lean_inc(v_a_2558_);
                                        leanh::lean_dec_ref_known(v___x_2539_, 1);
                                        v___x_2559_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3;
                                        leanh::lean_inc(v_json_2495_);
                                        v___x_2560_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_2495_, v___x_2559_);
                                        if leanh::lean_obj_tag(v___x_2560_) == 0 {
                                            leanh::lean_dec(v_a_2558_);
                                            leanh::lean_dec(v_a_2537_);
                                            leanh::lean_dec(v_a_2516_);
                                            leanh::lean_dec(v_json_2495_);
                                            v_a_2561_ = leanh::lean_ctor_get(v___x_2560_, 0);
                                            v_isSharedCheck_2570_ =
                                                (!leanh::lean_is_exclusive(v___x_2560_))
                                                    as u8;
                                            if v_isSharedCheck_2570_ == 0 {
                                                v___x_2563_ = v___x_2560_;
                                                v_isShared_2564_ = v_isSharedCheck_2570_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2561_);
                                                leanh::lean_dec(v___x_2560_);
                                                v___x_2563_ = leanh::lean_box(0);
                                                v_isShared_2564_ = v_isSharedCheck_2570_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_2560_) == 0 {
                                                leanh::lean_dec(v_a_2558_);
                                                leanh::lean_dec(v_a_2537_);
                                                leanh::lean_dec(v_a_2516_);
                                                leanh::lean_dec(v_json_2495_);
                                                v_a_2571_ =
                                                    leanh::lean_ctor_get(v___x_2560_, 0);
                                                v_isSharedCheck_2578_ =
                                                    (!leanh::lean_is_exclusive(v___x_2560_))
                                                        as u8;
                                                if v_isSharedCheck_2578_ == 0 {
                                                    v___x_2573_ = v___x_2560_;
                                                    v_isShared_2574_ = v_isSharedCheck_2578_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_2571_);
                                                    leanh::lean_dec(v___x_2560_);
                                                    v___x_2573_ = leanh::lean_box(0);
                                                    v_isShared_2574_ = v_isSharedCheck_2578_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_2579_ =
                                                    leanh::lean_ctor_get(v___x_2560_, 0);
                                                leanh::lean_inc(v_a_2579_);
                                                leanh::lean_dec_ref_known(v___x_2560_, 1);
                                                v___x_2580_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4;
                                                v___x_2581_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_json_2495_, v___x_2580_);
                                                if leanh::lean_obj_tag(v___x_2581_) == 0 {
                                                    leanh::lean_dec(v_a_2579_);
                                                    leanh::lean_dec(v_a_2558_);
                                                    leanh::lean_dec(v_a_2537_);
                                                    leanh::lean_dec(v_a_2516_);
                                                    v_a_2582_ =
                                                        leanh::lean_ctor_get(v___x_2581_, 0);
                                                    v_isSharedCheck_2591_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_2581_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2591_ == 0 {
                                                        v___x_2584_ = v___x_2581_;
                                                        v_isShared_2585_ = v_isSharedCheck_2591_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_2582_);
                                                        leanh::lean_dec(v___x_2581_);
                                                        v___x_2584_ = leanh::lean_box(0);
                                                        v_isShared_2585_ = v_isSharedCheck_2591_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if leanh::lean_obj_tag(v___x_2581_) == 0
                                                    {
                                                        leanh::lean_dec(v_a_2579_);
                                                        leanh::lean_dec(v_a_2558_);
                                                        leanh::lean_dec(v_a_2537_);
                                                        leanh::lean_dec(v_a_2516_);
                                                        v_a_2592_ = leanh::lean_ctor_get(
                                                            v___x_2581_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_2599_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_2581_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2599_ == 0 {
                                                            v___x_2594_ = v___x_2581_;
                                                            v_isShared_2595_ =
                                                                v_isSharedCheck_2599_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_2592_);
                                                            leanh::lean_dec(v___x_2581_);
                                                            v___x_2594_ = leanh::lean_box(0);
                                                            v_isShared_2595_ =
                                                                v_isSharedCheck_2599_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_2600_ = leanh::lean_ctor_get(
                                                            v___x_2581_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_2612_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_2581_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2612_ == 0 {
                                                            v___x_2602_ = v___x_2581_;
                                                            v_isShared_2603_ =
                                                                v_isSharedCheck_2612_;
                                                            state = 21;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_2600_);
                                                            leanh::lean_dec(v___x_2581_);
                                                            v___x_2602_ = leanh::lean_box(0);
                                                            v_isShared_2603_ =
                                                                v_isSharedCheck_2612_;
                                                            state = 21;
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
                }
            }
            1 => {
                v___x_2502_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7,
                );
                v___x_2503_ = lean_string_append(v___x_2502_, v_a_2498_);
                leanh::lean_dec(v_a_2498_);
                if v_isShared_2501_ == 0 {
                    leanh::lean_ctor_set(v___x_2500_, 0, v___x_2503_);
                    v___x_2505_ = v___x_2500_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2506_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
                    v___x_2505_ = v_reuseFailAlloc_2506_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2505_;
            }
            3 => {
                if v_isShared_2511_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2510_, 0);
                    v___x_2513_ = v___x_2510_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
                    v___x_2513_ = v_reuseFailAlloc_2514_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2513_;
            }
            5 => {
                v___x_2523_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11,
                );
                v___x_2524_ = lean_string_append(v___x_2523_, v_a_2519_);
                leanh::lean_dec(v_a_2519_);
                if v_isShared_2522_ == 0 {
                    leanh::lean_ctor_set(v___x_2521_, 0, v___x_2524_);
                    v___x_2526_ = v___x_2521_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2524_);
                    v___x_2526_ = v_reuseFailAlloc_2527_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2526_;
            }
            7 => {
                if v_isShared_2532_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2531_, 0);
                    v___x_2534_ = v___x_2531_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2535_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
                    v___x_2534_ = v_reuseFailAlloc_2535_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2534_;
            }
            9 => {
                v___x_2544_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15,
                );
                v___x_2545_ = lean_string_append(v___x_2544_, v_a_2540_);
                leanh::lean_dec(v_a_2540_);
                if v_isShared_2543_ == 0 {
                    leanh::lean_ctor_set(v___x_2542_, 0, v___x_2545_);
                    v___x_2547_ = v___x_2542_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2548_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
                    v___x_2547_ = v_reuseFailAlloc_2548_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2547_;
            }
            11 => {
                if v_isShared_2553_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2552_, 0);
                    v___x_2555_ = v___x_2552_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2556_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
                    v___x_2555_ = v_reuseFailAlloc_2556_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2555_;
            }
            13 => {
                v___x_2565_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19,
                );
                v___x_2566_ = lean_string_append(v___x_2565_, v_a_2561_);
                leanh::lean_dec(v_a_2561_);
                if v_isShared_2564_ == 0 {
                    leanh::lean_ctor_set(v___x_2563_, 0, v___x_2566_);
                    v___x_2568_ = v___x_2563_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
                    v___x_2568_ = v_reuseFailAlloc_2569_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2568_;
            }
            15 => {
                if v_isShared_2574_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2573_, 0);
                    v___x_2576_ = v___x_2573_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
                    v___x_2576_ = v_reuseFailAlloc_2577_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2576_;
            }
            17 => {
                v___x_2586_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24,
                );
                v___x_2587_ = lean_string_append(v___x_2586_, v_a_2582_);
                leanh::lean_dec(v_a_2582_);
                if v_isShared_2585_ == 0 {
                    leanh::lean_ctor_set(v___x_2584_, 0, v___x_2587_);
                    v___x_2589_ = v___x_2584_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2589_;
            }
            19 => {
                if v_isShared_2595_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2594_, 0);
                    v___x_2597_ = v___x_2594_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2598_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
                    v___x_2597_ = v_reuseFailAlloc_2598_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2597_;
            }
            21 => {
                v___x_2604_ = leanh::lean_alloc_ctor(0, 1, (4) as u32);
                leanh::lean_ctor_set(v___x_2604_, 0, v_a_2600_);
                v___x_2605_ = (leanh::lean_unbox(v_a_2516_) as u8);
                leanh::lean_dec(v_a_2516_);
                leanh::lean_ctor_set_uint8(
                    v___x_2604_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2605_,
                );
                v___x_2606_ = (leanh::lean_unbox(v_a_2537_) as u8);
                leanh::lean_dec(v_a_2537_);
                leanh::lean_ctor_set_uint8(
                    v___x_2604_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    v___x_2606_,
                );
                v___x_2607_ = (leanh::lean_unbox(v_a_2558_) as u8);
                leanh::lean_dec(v_a_2558_);
                leanh::lean_ctor_set_uint8(
                    v___x_2604_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                    v___x_2607_,
                );
                v___x_2608_ = (leanh::lean_unbox(v_a_2579_) as u8);
                leanh::lean_dec(v_a_2579_);
                leanh::lean_ctor_set_uint8(
                    v___x_2604_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 3) as u32,
                    v___x_2608_,
                );
                if v_isShared_2603_ == 0 {
                    leanh::lean_ctor_set(v___x_2602_, 0, v___x_2604_);
                    v___x_2610_ = v___x_2602_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2611_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2604_);
                    v___x_2610_ = v_reuseFailAlloc_2611_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2610_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_TextSync(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_TextSync(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_TextSync(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_TextSync(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_TextSync(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_TextSync(builtin);
}
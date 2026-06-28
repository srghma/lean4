// Lean compiler output
// Module: Lean.Data.Lsp.Workspace
// Imports: Lean.Data.Lsp.Basic
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getNat_x3f, l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
    l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::Basic::{
    initialize_Lean_Data_Lsp_Basic, runtime_initialize_Lean_Data_Lsp_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
};
pub static l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 114, 105, 0],
};
static mut l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2_value:
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
static mut l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instToJsonWorkspaceFolder_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonWorkspaceFolder: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value:
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
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value:
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
        87, 111, 114, 107, 115, 112, 97, 99, 101, 70, 111, 108, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
        6668733902101006929 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5_value:
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
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6053811214292724070 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10_value:
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
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5949480926448383572 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonWorkspaceFolder: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [103, 108, 111, 98, 80, 97, 116, 116, 101, 114, 110, 0],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        70, 105, 108, 101, 83, 121, 115, 116, 101, 109, 87, 97, 116, 99, 104, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_1:
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
            l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value:
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
            l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17539411788740541372 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13563531222688826382 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9_value:
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
    m_data: [107, 105, 110, 100, 0],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10_value:
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
    m_data: [107, 105, 110, 100, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10_value)
            as *mut crate::leanh::LeanObject,
        13532862018704899050 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonFileSystemWatcher: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonFileSystemWatcher_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonFileSystemWatcher: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_FileSystemWatcher_create: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Lsp_FileSystemWatcher_change: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Lsp_FileSystemWatcher_delete: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [119, 97, 116, 99, 104, 101, 114, 115, 0]};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1_value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [68, 105, 100, 67, 104, 97, 110, 103, 101, 87, 97, 116, 99, 104, 101, 100, 70, 105, 108, 101, 115, 82, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 79, 112, 116, 105, 111, 110, 115, 0]};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value) as *mut crate::leanh::LeanObject,6773744487318448338 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1_value) as *mut crate::leanh::LeanObject,15581767320145518792 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0_value) as *mut crate::leanh::LeanObject,10377628074256779973 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 49, 44, 32, 50, 44, 32, 111, 114, 32, 51, 44,
        32, 103, 111, 116, 32, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileChangeType___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonFileChangeType___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonFileChangeType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonFileChangeType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonFileChangeType___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instToJsonFileChangeType___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonFileChangeType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileChangeType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonFileChangeType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileChangeType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [70, 105, 108, 101, 69, 118, 101, 110, 116, 0],
};
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14989506372905311455 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6_value:
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
    m_data: [116, 121, 112, 101, 0],
};
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6_value)
            as *mut crate::leanh::LeanObject,
        11503787708459150704 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonFileEvent___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonFileEvent_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonFileEvent___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonFileEvent: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonFileEvent___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonFileEvent_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonFileEvent___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileEvent___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonFileEvent: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileEvent___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0_value:
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
    m_data: [99, 104, 97, 110, 103, 101, 115, 0],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        68, 105, 100, 67, 104, 97, 110, 103, 101, 87, 97, 116, 99, 104, 101, 100, 70, 105, 108,
        101, 115, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value:
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
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        403225530036258855 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5_value:
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
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        729844717526787275 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(
    mut v_a_841_: *mut crate::leanh::LeanObject,
    mut v_a_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_841_) == 0 {
                    v___x_843_ = lean_array_to_list(v_a_842_);
                    return v___x_843_;
                } else {
                    v_head_844_ = crate::leanh::lean_ctor_get(v_a_841_, 0);
                    crate::leanh::lean_inc(v_head_844_);
                    v_tail_845_ = crate::leanh::lean_ctor_get(v_a_841_, 1);
                    crate::leanh::lean_inc(v_tail_845_);
                    crate::leanh::lean_dec_ref_known(v_a_841_, 2);
                    v___x_846_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_842_,
                        v_head_844_,
                    );
                    v_a_841_ = v_tail_845_;
                    v_a_842_ = v___x_846_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(
    mut v_x_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_857_: u8 = 0;
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_853_ = crate::leanh::lean_ctor_get(v_x_852_, 0);
                v_name_854_ = crate::leanh::lean_ctor_get(v_x_852_, 1);
                v_isSharedCheck_874_ = (!crate::leanh::lean_is_exclusive(v_x_852_)) as u8;
                if v_isSharedCheck_874_ == 0 {
                    v___x_856_ = v_x_852_;
                    v_isShared_857_ = v_isSharedCheck_874_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_854_);
                    crate::leanh::lean_inc(v_uri_853_);
                    crate::leanh::lean_dec(v_x_852_);
                    v___x_856_ = crate::leanh::lean_box(0);
                    v_isShared_857_ = v_isSharedCheck_874_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_858_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0;
                v___x_859_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_859_, 0, v_uri_853_);
                if v_isShared_857_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_856_, 1, v___x_859_);
                    crate::leanh::lean_ctor_set(v___x_856_, 0, v___x_858_);
                    v___x_861_ = v___x_856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_859_);
                    v___x_861_ = v_reuseFailAlloc_873_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_862_ = crate::leanh::lean_box(0);
                v___x_863_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_863_, 0, v___x_861_);
                crate::leanh::lean_ctor_set(v___x_863_, 1, v___x_862_);
                v___x_864_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1;
                v___x_865_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_865_, 0, v_name_854_);
                v___x_866_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_866_, 0, v___x_864_);
                crate::leanh::lean_ctor_set(v___x_866_, 1, v___x_865_);
                v___x_867_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_867_, 0, v___x_866_);
                crate::leanh::lean_ctor_set(v___x_867_, 1, v___x_862_);
                v___x_868_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_868_, 0, v___x_867_);
                crate::leanh::lean_ctor_set(v___x_868_, 1, v___x_862_);
                v___x_869_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_869_, 0, v___x_863_);
                crate::leanh::lean_ctor_set(v___x_869_, 1, v___x_868_);
                v___x_870_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2;
                v___x_871_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_869_, v___x_870_);
                v___x_872_ = l_Lean_Json_mkObj(v___x_871_);
                crate::leanh::lean_dec(v___x_871_);
                return v___x_872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(
    mut v_j_877_: *mut crate::leanh::LeanObject,
    mut v_k_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = l_Lean_Json_getObjValD(v_j_877_, v_k_878_);
    v___x_880_ = l_Lean_Json_getStr_x3f(v___x_879_);
    return v___x_880_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0___boxed(
    mut v_j_881_: *mut crate::leanh::LeanObject,
    mut v_k_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_883_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(
            v_j_881_, v_k_882_,
        );
    crate::leanh::lean_dec_ref(v_k_882_);
    return v_res_883_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_891_: u8 = 0;
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = 1;
    v___x_892_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3;
    v___x_893_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_892_, v___x_891_);
    return v___x_893_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_895_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5;
    v___x_896_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4,
    );
    v___x_897_ = lean_string_append(v___x_896_, v___x_895_);
    return v___x_897_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_900_ = 1;
    v___x_901_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7;
    v___x_902_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_901_, v___x_900_);
    return v___x_902_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8,
    );
    v___x_904_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6,
    );
    v___x_905_ = lean_string_append(v___x_904_, v___x_903_);
    return v___x_905_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_907_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_908_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9,
    );
    v___x_909_ = lean_string_append(v___x_908_, v___x_907_);
    return v___x_909_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_912_: u8 = 0;
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = 1;
    v___x_913_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12;
    v___x_914_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_913_, v___x_912_);
    return v___x_914_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_915_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13,
    );
    v___x_916_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6,
    );
    v___x_917_ = lean_string_append(v___x_916_, v___x_915_);
    return v___x_917_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_919_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14,
    );
    v___x_920_ = lean_string_append(v___x_919_, v___x_918_);
    return v___x_920_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson(
    mut v_json_921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut v_a_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_941_: u8 = 0;
    let mut v_a_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_954_: u8 = 0;
    let mut v_a_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_958_: u8 = 0;
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_962_: u8 = 0;
    let mut v_a_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_966_: u8 = 0;
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_922_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0;
                crate::leanh::lean_inc(v_json_921_);
                v___x_923_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_921_, v___x_922_);
                if crate::leanh::lean_obj_tag(v___x_923_) == 0 {
                    crate::leanh::lean_dec(v_json_921_);
                    v_a_924_ = crate::leanh::lean_ctor_get(v___x_923_, 0);
                    v_isSharedCheck_933_ = (!crate::leanh::lean_is_exclusive(v___x_923_)) as u8;
                    if v_isSharedCheck_933_ == 0 {
                        v___x_926_ = v___x_923_;
                        v_isShared_927_ = v_isSharedCheck_933_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_924_);
                        crate::leanh::lean_dec(v___x_923_);
                        v___x_926_ = crate::leanh::lean_box(0);
                        v_isShared_927_ = v_isSharedCheck_933_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_923_) == 0 {
                        crate::leanh::lean_dec(v_json_921_);
                        v_a_934_ = crate::leanh::lean_ctor_get(v___x_923_, 0);
                        v_isSharedCheck_941_ = (!crate::leanh::lean_is_exclusive(v___x_923_)) as u8;
                        if v_isSharedCheck_941_ == 0 {
                            v___x_936_ = v___x_923_;
                            v_isShared_937_ = v_isSharedCheck_941_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_934_);
                            crate::leanh::lean_dec(v___x_923_);
                            v___x_936_ = crate::leanh::lean_box(0);
                            v_isShared_937_ = v_isSharedCheck_941_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_942_ = crate::leanh::lean_ctor_get(v___x_923_, 0);
                        crate::leanh::lean_inc(v_a_942_);
                        crate::leanh::lean_dec_ref_known(v___x_923_, 1);
                        v___x_943_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1;
                        v___x_944_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_921_, v___x_943_);
                        if crate::leanh::lean_obj_tag(v___x_944_) == 0 {
                            crate::leanh::lean_dec(v_a_942_);
                            v_a_945_ = crate::leanh::lean_ctor_get(v___x_944_, 0);
                            v_isSharedCheck_954_ =
                                (!crate::leanh::lean_is_exclusive(v___x_944_)) as u8;
                            if v_isSharedCheck_954_ == 0 {
                                v___x_947_ = v___x_944_;
                                v_isShared_948_ = v_isSharedCheck_954_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_945_);
                                crate::leanh::lean_dec(v___x_944_);
                                v___x_947_ = crate::leanh::lean_box(0);
                                v_isShared_948_ = v_isSharedCheck_954_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_944_) == 0 {
                                crate::leanh::lean_dec(v_a_942_);
                                v_a_955_ = crate::leanh::lean_ctor_get(v___x_944_, 0);
                                v_isSharedCheck_962_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_944_)) as u8;
                                if v_isSharedCheck_962_ == 0 {
                                    v___x_957_ = v___x_944_;
                                    v_isShared_958_ = v_isSharedCheck_962_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_955_);
                                    crate::leanh::lean_dec(v___x_944_);
                                    v___x_957_ = crate::leanh::lean_box(0);
                                    v_isShared_958_ = v_isSharedCheck_962_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_963_ = crate::leanh::lean_ctor_get(v___x_944_, 0);
                                v_isSharedCheck_971_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_944_)) as u8;
                                if v_isSharedCheck_971_ == 0 {
                                    v___x_965_ = v___x_944_;
                                    v_isShared_966_ = v_isSharedCheck_971_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_963_);
                                    crate::leanh::lean_dec(v___x_944_);
                                    v___x_965_ = crate::leanh::lean_box(0);
                                    v_isShared_966_ = v_isSharedCheck_971_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_928_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11,
                );
                v___x_929_ = lean_string_append(v___x_928_, v_a_924_);
                crate::leanh::lean_dec(v_a_924_);
                if v_isShared_927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_926_, 0, v___x_929_);
                    v___x_931_ = v___x_926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
                    v___x_931_ = v_reuseFailAlloc_932_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_931_;
            }
            3 => {
                if v_isShared_937_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_936_, 0);
                    v___x_939_ = v___x_936_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_940_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
                    v___x_939_ = v_reuseFailAlloc_940_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_939_;
            }
            5 => {
                v___x_949_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15,
                );
                v___x_950_ = lean_string_append(v___x_949_, v_a_945_);
                crate::leanh::lean_dec(v_a_945_);
                if v_isShared_948_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_947_, 0, v___x_950_);
                    v___x_952_ = v___x_947_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_953_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
                    v___x_952_ = v_reuseFailAlloc_953_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_952_;
            }
            7 => {
                if v_isShared_958_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_957_, 0);
                    v___x_960_ = v___x_957_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_961_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
                    v___x_960_ = v_reuseFailAlloc_961_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_960_;
            }
            9 => {
                v___x_967_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_967_, 0, v_a_942_);
                crate::leanh::lean_ctor_set(v___x_967_, 1, v_a_963_);
                if v_isShared_966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_965_, 0, v___x_967_);
                    v___x_969_ = v___x_965_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_970_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
                    v___x_969_ = v_reuseFailAlloc_970_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(
    mut v_x_976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_982_: u8 = 0;
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_986_: u8 = 0;
    let mut v_a_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_976_) == 0 {
                    v___x_977_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0;
                    return v___x_977_;
                } else {
                    v___x_978_ = l_Lean_Json_getNat_x3f(v_x_976_);
                    if crate::leanh::lean_obj_tag(v___x_978_) == 0 {
                        v_a_979_ = crate::leanh::lean_ctor_get(v___x_978_, 0);
                        v_isSharedCheck_986_ = (!crate::leanh::lean_is_exclusive(v___x_978_)) as u8;
                        if v_isSharedCheck_986_ == 0 {
                            v___x_981_ = v___x_978_;
                            v_isShared_982_ = v_isSharedCheck_986_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_979_);
                            crate::leanh::lean_dec(v___x_978_);
                            v___x_981_ = crate::leanh::lean_box(0);
                            v_isShared_982_ = v_isSharedCheck_986_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_987_ = crate::leanh::lean_ctor_get(v___x_978_, 0);
                        v_isSharedCheck_995_ = (!crate::leanh::lean_is_exclusive(v___x_978_)) as u8;
                        if v_isSharedCheck_995_ == 0 {
                            v___x_989_ = v___x_978_;
                            v_isShared_990_ = v_isSharedCheck_995_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_987_);
                            crate::leanh::lean_dec(v___x_978_);
                            v___x_989_ = crate::leanh::lean_box(0);
                            v_isShared_990_ = v_isSharedCheck_995_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_982_ == 0 {
                    v___x_984_ = v___x_981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
                    v___x_984_ = v_reuseFailAlloc_985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_984_;
            }
            3 => {
                v___x_991_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_991_, 0, v_a_987_);
                if v_isShared_990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_989_, 0, v___x_991_);
                    v___x_993_ = v___x_989_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
                    v___x_993_ = v_reuseFailAlloc_994_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(
    mut v_j_996_: *mut crate::leanh::LeanObject,
    mut v_k_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = l_Lean_Json_getObjValD(v_j_996_, v_k_997_);
    v___x_999_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(v___x_998_);
    return v___x_999_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0___boxed(
    mut v_j_1000_: *mut crate::leanh::LeanObject,
    mut v_k_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1002_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(v_j_1000_, v_k_1001_);
    crate::leanh::lean_dec_ref(v_k_1001_);
    return v_res_1002_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1009_: u8 = 0;
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = 1;
    v___x_1010_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2;
    v___x_1011_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1010_, v___x_1009_);
    return v___x_1011_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1012_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5;
    v___x_1013_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3,
    );
    v___x_1014_ = lean_string_append(v___x_1013_, v___x_1012_);
    return v___x_1014_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1017_: u8 = 0;
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1017_ = 1;
    v___x_1018_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5;
    v___x_1019_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1018_, v___x_1017_);
    return v___x_1019_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1020_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6,
    );
    v___x_1021_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4,
    );
    v___x_1022_ = lean_string_append(v___x_1021_, v___x_1020_);
    return v___x_1022_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1024_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7,
    );
    v___x_1025_ = lean_string_append(v___x_1024_, v___x_1023_);
    return v___x_1025_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1030_ = 1;
    v___x_1031_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11;
    v___x_1032_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1031_, v___x_1030_);
    return v___x_1032_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12,
    );
    v___x_1034_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4,
    );
    v___x_1035_ = lean_string_append(v___x_1034_, v___x_1033_);
    return v___x_1035_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1036_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1037_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13,
    );
    v___x_1038_ = lean_string_append(v___x_1037_, v___x_1036_);
    return v___x_1038_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(
    mut v_json_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1045_: u8 = 0;
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1051_: u8 = 0;
    let mut v_a_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1059_: u8 = 0;
    let mut v_a_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1072_: u8 = 0;
    let mut v_a_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1076_: u8 = 0;
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v_a_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1084_: u8 = 0;
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1040_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0;
                crate::leanh::lean_inc(v_json_1039_);
                v___x_1041_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_1039_, v___x_1040_);
                if crate::leanh::lean_obj_tag(v___x_1041_) == 0 {
                    crate::leanh::lean_dec(v_json_1039_);
                    v_a_1042_ = crate::leanh::lean_ctor_get(v___x_1041_, 0);
                    v_isSharedCheck_1051_ = (!crate::leanh::lean_is_exclusive(v___x_1041_)) as u8;
                    if v_isSharedCheck_1051_ == 0 {
                        v___x_1044_ = v___x_1041_;
                        v_isShared_1045_ = v_isSharedCheck_1051_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1042_);
                        crate::leanh::lean_dec(v___x_1041_);
                        v___x_1044_ = crate::leanh::lean_box(0);
                        v_isShared_1045_ = v_isSharedCheck_1051_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_1041_) == 0 {
                        crate::leanh::lean_dec(v_json_1039_);
                        v_a_1052_ = crate::leanh::lean_ctor_get(v___x_1041_, 0);
                        v_isSharedCheck_1059_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1041_)) as u8;
                        if v_isSharedCheck_1059_ == 0 {
                            v___x_1054_ = v___x_1041_;
                            v_isShared_1055_ = v_isSharedCheck_1059_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1052_);
                            crate::leanh::lean_dec(v___x_1041_);
                            v___x_1054_ = crate::leanh::lean_box(0);
                            v_isShared_1055_ = v_isSharedCheck_1059_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1060_ = crate::leanh::lean_ctor_get(v___x_1041_, 0);
                        crate::leanh::lean_inc(v_a_1060_);
                        crate::leanh::lean_dec_ref_known(v___x_1041_, 1);
                        v___x_1061_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9;
                        v___x_1062_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(v_json_1039_, v___x_1061_);
                        if crate::leanh::lean_obj_tag(v___x_1062_) == 0 {
                            crate::leanh::lean_dec(v_a_1060_);
                            v_a_1063_ = crate::leanh::lean_ctor_get(v___x_1062_, 0);
                            v_isSharedCheck_1072_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1062_)) as u8;
                            if v_isSharedCheck_1072_ == 0 {
                                v___x_1065_ = v___x_1062_;
                                v_isShared_1066_ = v_isSharedCheck_1072_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1063_);
                                crate::leanh::lean_dec(v___x_1062_);
                                v___x_1065_ = crate::leanh::lean_box(0);
                                v_isShared_1066_ = v_isSharedCheck_1072_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_1062_) == 0 {
                                crate::leanh::lean_dec(v_a_1060_);
                                v_a_1073_ = crate::leanh::lean_ctor_get(v___x_1062_, 0);
                                v_isSharedCheck_1080_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1062_)) as u8;
                                if v_isSharedCheck_1080_ == 0 {
                                    v___x_1075_ = v___x_1062_;
                                    v_isShared_1076_ = v_isSharedCheck_1080_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1073_);
                                    crate::leanh::lean_dec(v___x_1062_);
                                    v___x_1075_ = crate::leanh::lean_box(0);
                                    v_isShared_1076_ = v_isSharedCheck_1080_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_1081_ = crate::leanh::lean_ctor_get(v___x_1062_, 0);
                                v_isSharedCheck_1089_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1062_)) as u8;
                                if v_isSharedCheck_1089_ == 0 {
                                    v___x_1083_ = v___x_1062_;
                                    v_isShared_1084_ = v_isSharedCheck_1089_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1081_);
                                    crate::leanh::lean_dec(v___x_1062_);
                                    v___x_1083_ = crate::leanh::lean_box(0);
                                    v_isShared_1084_ = v_isSharedCheck_1089_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1046_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8,
                );
                v___x_1047_ = lean_string_append(v___x_1046_, v_a_1042_);
                crate::leanh::lean_dec(v_a_1042_);
                if v_isShared_1045_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1044_, 0, v___x_1047_);
                    v___x_1049_ = v___x_1044_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1050_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
                    v___x_1049_ = v_reuseFailAlloc_1050_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1049_;
            }
            3 => {
                if v_isShared_1055_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1054_, 0);
                    v___x_1057_ = v___x_1054_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
                    v___x_1057_ = v_reuseFailAlloc_1058_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1057_;
            }
            5 => {
                v___x_1067_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14,
                );
                v___x_1068_ = lean_string_append(v___x_1067_, v_a_1063_);
                crate::leanh::lean_dec(v_a_1063_);
                if v_isShared_1066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1065_, 0, v___x_1068_);
                    v___x_1070_ = v___x_1065_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1071_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
                    v___x_1070_ = v_reuseFailAlloc_1071_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1070_;
            }
            7 => {
                if v_isShared_1076_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1075_, 0);
                    v___x_1078_ = v___x_1075_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
                    v___x_1078_ = v_reuseFailAlloc_1079_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1078_;
            }
            9 => {
                v___x_1085_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1085_, 0, v_a_1060_);
                crate::leanh::lean_ctor_set(v___x_1085_, 1, v_a_1081_);
                if v_isShared_1084_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1083_, 0, v___x_1085_);
                    v___x_1087_ = v___x_1083_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1088_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
                    v___x_1087_ = v_reuseFailAlloc_1088_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(
    mut v_k_1092_: *mut crate::leanh::LeanObject,
    mut v_x_1093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1093_) == 0 {
                    crate::leanh::lean_dec_ref(v_k_1092_);
                    v___x_1094_ = crate::leanh::lean_box(0);
                    return v___x_1094_;
                } else {
                    v_val_1095_ = crate::leanh::lean_ctor_get(v_x_1093_, 0);
                    v_isSharedCheck_1106_ = (!crate::leanh::lean_is_exclusive(v_x_1093_)) as u8;
                    if v_isSharedCheck_1106_ == 0 {
                        v___x_1097_ = v_x_1093_;
                        v_isShared_1098_ = v_isSharedCheck_1106_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1095_);
                        crate::leanh::lean_dec(v_x_1093_);
                        v___x_1097_ = crate::leanh::lean_box(0);
                        v_isShared_1098_ = v_isSharedCheck_1106_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1099_ = l_Lean_JsonNumber_fromNat(v_val_1095_);
                if v_isShared_1098_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1097_, 2);
                    crate::leanh::lean_ctor_set(v___x_1097_, 0, v___x_1099_);
                    v___x_1101_ = v___x_1097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1099_);
                    v___x_1101_ = v_reuseFailAlloc_1105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1102_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1102_, 0, v_k_1092_);
                crate::leanh::lean_ctor_set(v___x_1102_, 1, v___x_1101_);
                v___x_1103_ = crate::leanh::lean_box(0);
                v___x_1104_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1104_, 0, v___x_1102_);
                crate::leanh::lean_ctor_set(v___x_1104_, 1, v___x_1103_);
                return v___x_1104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(
    mut v_x_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_globPattern_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1112_: u8 = 0;
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_globPattern_1108_ = crate::leanh::lean_ctor_get(v_x_1107_, 0);
                v_kind_x3f_1109_ = crate::leanh::lean_ctor_get(v_x_1107_, 1);
                v_isSharedCheck_1127_ = (!crate::leanh::lean_is_exclusive(v_x_1107_)) as u8;
                if v_isSharedCheck_1127_ == 0 {
                    v___x_1111_ = v_x_1107_;
                    v_isShared_1112_ = v_isSharedCheck_1127_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_x3f_1109_);
                    crate::leanh::lean_inc(v_globPattern_1108_);
                    crate::leanh::lean_dec(v_x_1107_);
                    v___x_1111_ = crate::leanh::lean_box(0);
                    v_isShared_1112_ = v_isSharedCheck_1127_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1113_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0;
                v___x_1114_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1114_, 0, v_globPattern_1108_);
                if v_isShared_1112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1111_, 1, v___x_1114_);
                    crate::leanh::lean_ctor_set(v___x_1111_, 0, v___x_1113_);
                    v___x_1116_ = v___x_1111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1126_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 1, v___x_1114_);
                    v___x_1116_ = v_reuseFailAlloc_1126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1117_ = crate::leanh::lean_box(0);
                v___x_1118_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1118_, 0, v___x_1116_);
                crate::leanh::lean_ctor_set(v___x_1118_, 1, v___x_1117_);
                v___x_1119_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9;
                v___x_1120_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(
                        v___x_1119_,
                        v_kind_x3f_1109_,
                    );
                v___x_1121_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1121_, 0, v___x_1120_);
                crate::leanh::lean_ctor_set(v___x_1121_, 1, v___x_1117_);
                v___x_1122_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1122_, 0, v___x_1118_);
                crate::leanh::lean_ctor_set(v___x_1122_, 1, v___x_1121_);
                v___x_1123_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2;
                v___x_1124_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_1122_, v___x_1123_);
                v___x_1125_ = l_Lean_Json_mkObj(v___x_1124_);
                crate::leanh::lean_dec(v___x_1124_);
                return v___x_1125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_FileSystemWatcher_create() -> *mut crate::leanh::LeanObject {
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1130_ = crate::leanh::lean_unsigned_to_nat(1);
    return v___x_1130_;
}
pub unsafe fn _init_l_Lean_Lsp_FileSystemWatcher_change() -> *mut crate::leanh::LeanObject {
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = crate::leanh::lean_unsigned_to_nat(2);
    return v___x_1131_;
}
pub unsafe fn _init_l_Lean_Lsp_FileSystemWatcher_delete() -> *mut crate::leanh::LeanObject {
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1132_ = crate::leanh::lean_unsigned_to_nat(4);
    return v___x_1132_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(
    mut v_sz_1133_: usize,
    mut v_i_1134_: usize,
    mut v_bs_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_a_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: usize = 0;
    let mut v___x_1152_: usize = 0;
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1136_ = lean_usize_dec_lt(v_i_1134_, v_sz_1133_);
                if v___x_1136_ == 0 {
                    v___x_1137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1137_, 0, v_bs_1135_);
                    return v___x_1137_;
                } else {
                    v_v_1138_ = lean_array_uget_borrowed(v_bs_1135_, v_i_1134_);
                    crate::leanh::lean_inc(v_v_1138_);
                    v___x_1139_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(v_v_1138_);
                    if crate::leanh::lean_obj_tag(v___x_1139_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_1135_);
                        v_a_1140_ = crate::leanh::lean_ctor_get(v___x_1139_, 0);
                        v_isSharedCheck_1147_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1139_)) as u8;
                        if v_isSharedCheck_1147_ == 0 {
                            v___x_1142_ = v___x_1139_;
                            v_isShared_1143_ = v_isSharedCheck_1147_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1140_);
                            crate::leanh::lean_dec(v___x_1139_);
                            v___x_1142_ = crate::leanh::lean_box(0);
                            v_isShared_1143_ = v_isSharedCheck_1147_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1148_ = crate::leanh::lean_ctor_get(v___x_1139_, 0);
                        crate::leanh::lean_inc(v_a_1148_);
                        crate::leanh::lean_dec_ref_known(v___x_1139_, 1);
                        v___x_1149_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1150_ = lean_array_uset(v_bs_1135_, v_i_1134_, v___x_1149_);
                        v___x_1151_ = 1usize;
                        v___x_1152_ = lean_usize_add(v_i_1134_, v___x_1151_);
                        v___x_1153_ = lean_array_uset(v_bs_x27_1150_, v_i_1134_, v_a_1148_);
                        v_i_1134_ = v___x_1152_;
                        v_bs_1135_ = v___x_1153_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1143_ == 0 {
                    v___x_1145_ = v___x_1142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1___boxed(
    mut v_sz_1155_: *mut crate::leanh::LeanObject,
    mut v_i_1156_: *mut crate::leanh::LeanObject,
    mut v_bs_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1158_: usize = 0;
    let mut v_i_boxed_1159_: usize = 0;
    let mut v_res_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1158_ = crate::leanh::lean_unbox_usize(v_sz_1155_);
    crate::leanh::lean_dec(v_sz_1155_);
    v_i_boxed_1159_ = crate::leanh::lean_unbox_usize(v_i_1156_);
    crate::leanh::lean_dec(v_i_1156_);
    v_res_1160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1158_, v_i_boxed_1159_, v_bs_1157_);
    return v_res_1160_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(
    mut v_x_1163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1163_) == 4 {
        let mut v_elems_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1165_: usize = 0;
        let mut v___x_1166_: usize = 0;
        let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_1164_ = crate::leanh::lean_ctor_get(v_x_1163_, 0);
        crate::leanh::lean_inc_ref(v_elems_1164_);
        crate::leanh::lean_dec_ref_known(v_x_1163_, 1);
        v_sz_1165_ = lean_array_size(v_elems_1164_);
        v___x_1166_ = 0usize;
        v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_1165_, v___x_1166_, v_elems_1164_);
        return v___x_1167_;
    } else {
        let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1168_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0;
        v___x_1169_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_1170_ = l_Lean_Json_pretty(v_x_1163_, v___x_1169_);
        v___x_1171_ = lean_string_append(v___x_1168_, v___x_1170_);
        crate::leanh::lean_dec_ref(v___x_1170_);
        v___x_1172_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1;
        v___x_1173_ = lean_string_append(v___x_1171_, v___x_1172_);
        v___x_1174_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1174_, 0, v___x_1173_);
        return v___x_1174_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(
    mut v_j_1175_: *mut crate::leanh::LeanObject,
    mut v_k_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Json_getObjValD(v_j_1175_, v_k_1176_);
    v___x_1178_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(v___x_1177_);
    return v___x_1178_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0___boxed(
    mut v_j_1179_: *mut crate::leanh::LeanObject,
    mut v_k_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(v_j_1179_, v_k_1180_);
    crate::leanh::lean_dec_ref(v_k_1180_);
    return v_res_1181_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1188_: u8 = 0;
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1188_ = 1;
    v___x_1189_ =
        l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2;
    v___x_1190_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1189_, v___x_1188_);
    return v___x_1190_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1191_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5;
    v___x_1192_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3);
    v___x_1193_ = lean_string_append(v___x_1192_, v___x_1191_);
    return v___x_1193_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1196_ = 1;
    v___x_1197_ =
        l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5;
    v___x_1198_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1197_, v___x_1196_);
    return v___x_1198_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1199_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6);
    v___x_1200_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4);
    v___x_1201_ = lean_string_append(v___x_1200_, v___x_1199_);
    return v___x_1201_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1203_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7);
    v___x_1204_ = lean_string_append(v___x_1203_, v___x_1202_);
    return v___x_1204_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson(
    mut v_json_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1211_: u8 = 0;
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut v_a_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut v_a_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1229_: u8 = 0;
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1206_ = l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0;
                v___x_1207_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(v_json_1205_, v___x_1206_);
                if crate::leanh::lean_obj_tag(v___x_1207_) == 0 {
                    v_a_1208_ = crate::leanh::lean_ctor_get(v___x_1207_, 0);
                    v_isSharedCheck_1217_ = (!crate::leanh::lean_is_exclusive(v___x_1207_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1210_ = v___x_1207_;
                        v_isShared_1211_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1208_);
                        crate::leanh::lean_dec(v___x_1207_);
                        v___x_1210_ = crate::leanh::lean_box(0);
                        v_isShared_1211_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_1207_) == 0 {
                        v_a_1218_ = crate::leanh::lean_ctor_get(v___x_1207_, 0);
                        v_isSharedCheck_1225_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1207_)) as u8;
                        if v_isSharedCheck_1225_ == 0 {
                            v___x_1220_ = v___x_1207_;
                            v_isShared_1221_ = v_isSharedCheck_1225_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1218_);
                            crate::leanh::lean_dec(v___x_1207_);
                            v___x_1220_ = crate::leanh::lean_box(0);
                            v_isShared_1221_ = v_isSharedCheck_1225_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1226_ = crate::leanh::lean_ctor_get(v___x_1207_, 0);
                        v_isSharedCheck_1233_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1207_)) as u8;
                        if v_isSharedCheck_1233_ == 0 {
                            v___x_1228_ = v___x_1207_;
                            v_isShared_1229_ = v_isSharedCheck_1233_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1226_);
                            crate::leanh::lean_dec(v___x_1207_);
                            v___x_1228_ = crate::leanh::lean_box(0);
                            v_isShared_1229_ = v_isSharedCheck_1233_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1212_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8);
                v___x_1213_ = lean_string_append(v___x_1212_, v_a_1208_);
                crate::leanh::lean_dec(v_a_1208_);
                if v_isShared_1211_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1210_, 0, v___x_1213_);
                    v___x_1215_ = v___x_1210_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_1220_, 0);
                    v___x_1223_ = v___x_1220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
                    v___x_1223_ = v_reuseFailAlloc_1224_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1223_;
            }
            5 => {
                if v_isShared_1229_ == 0 {
                    v___x_1231_ = v___x_1228_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
                    v___x_1231_ = v_reuseFailAlloc_1232_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(
    mut v_sz_1236_: usize,
    mut v_i_1237_: usize,
    mut v_bs_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1239_: u8 = 0;
    let mut v_v_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1239_ = lean_usize_dec_lt(v_i_1237_, v_sz_1236_);
                if v___x_1239_ == 0 {
                    return v_bs_1238_;
                } else {
                    v_v_1240_ = lean_array_uget(v_bs_1238_, v_i_1237_);
                    v___x_1241_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1242_ = lean_array_uset(v_bs_1238_, v_i_1237_, v___x_1241_);
                    v___x_1243_ = l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(v_v_1240_);
                    v___x_1244_ = 1usize;
                    v___x_1245_ = lean_usize_add(v_i_1237_, v___x_1244_);
                    v___x_1246_ = lean_array_uset(v_bs_x27_1242_, v_i_1237_, v___x_1243_);
                    v_i_1237_ = v___x_1245_;
                    v_bs_1238_ = v___x_1246_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0___boxed(
    mut v_sz_1248_: *mut crate::leanh::LeanObject,
    mut v_i_1249_: *mut crate::leanh::LeanObject,
    mut v_bs_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1251_: usize = 0;
    let mut v_i_boxed_1252_: usize = 0;
    let mut v_res_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1251_ = crate::leanh::lean_unbox_usize(v_sz_1248_);
    crate::leanh::lean_dec(v_sz_1248_);
    v_i_boxed_1252_ = crate::leanh::lean_unbox_usize(v_i_1249_);
    crate::leanh::lean_dec(v_i_1249_);
    v_res_1253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_boxed_1251_, v_i_boxed_1252_, v_bs_1250_);
    return v_res_1253_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(
    mut v_a_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1255_: usize = 0;
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_1255_ = lean_array_size(v_a_1254_);
    v___x_1256_ = 0usize;
    v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_1255_, v___x_1256_, v_a_1254_);
    v___x_1258_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1258_, 0, v___x_1257_);
    return v___x_1258_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson(
    mut v_x_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1260_ =
        l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0;
    v___x_1261_ = l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(v_x_1259_);
    v___x_1262_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1262_, 0, v___x_1260_);
    crate::leanh::lean_ctor_set(v___x_1262_, 1, v___x_1261_);
    v___x_1263_ = crate::leanh::lean_box(0);
    v___x_1264_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1264_, 0, v___x_1262_);
    crate::leanh::lean_ctor_set(v___x_1264_, 1, v___x_1263_);
    v___x_1265_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1265_, 0, v___x_1264_);
    crate::leanh::lean_ctor_set(v___x_1265_, 1, v___x_1263_);
    v___x_1266_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2;
    v___x_1267_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_1265_, v___x_1266_);
    v___x_1268_ = l_Lean_Json_mkObj(v___x_1267_);
    crate::leanh::lean_dec(v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorIdx(
    mut v_x_1271_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1271_ {
        0 => {
            let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1272_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1272_;
        }
        1 => {
            let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1273_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1273_;
        }
        _ => {
            let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1274_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1274_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorIdx___boxed(
    mut v_x_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1276_: u8 = 0;
    let mut v_res_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1276_ = (crate::leanh::lean_unbox(v_x_1275_) as u8);
    v_res_1277_ = l_Lean_Lsp_FileChangeType_ctorIdx(v_x_boxed_1276_);
    return v_res_1277_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_toCtorIdx(
    mut v_x_1278_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1279_ = l_Lean_Lsp_FileChangeType_ctorIdx(v_x_1278_);
    return v___x_1279_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_toCtorIdx___boxed(
    mut v_x_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1281_: u8 = 0;
    let mut v_res_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1281_ = (crate::leanh::lean_unbox(v_x_1280_) as u8);
    v_res_1282_ = l_Lean_Lsp_FileChangeType_toCtorIdx(v_x_4__boxed_1281_);
    return v_res_1282_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorElim___redArg(
    mut v_k_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1283_);
    return v_k_1283_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorElim___redArg___boxed(
    mut v_k_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_Lean_Lsp_FileChangeType_ctorElim___redArg(v_k_1284_);
    crate::leanh::lean_dec(v_k_1284_);
    return v_res_1285_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorElim(
    mut v_motive_1286_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1287_: *mut crate::leanh::LeanObject,
    mut v_t_1288_: u8,
    mut v_h_1289_: *mut crate::leanh::LeanObject,
    mut v_k_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1290_);
    return v_k_1290_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorElim___boxed(
    mut v_motive_1291_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1292_: *mut crate::leanh::LeanObject,
    mut v_t_1293_: *mut crate::leanh::LeanObject,
    mut v_h_1294_: *mut crate::leanh::LeanObject,
    mut v_k_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1296_: u8 = 0;
    let mut v_res_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1296_ = (crate::leanh::lean_unbox(v_t_1293_) as u8);
    v_res_1297_ = l_Lean_Lsp_FileChangeType_ctorElim(
        v_motive_1291_,
        v_ctorIdx_1292_,
        v_t_boxed_1296_,
        v_h_1294_,
        v_k_1295_,
    );
    crate::leanh::lean_dec(v_k_1295_);
    crate::leanh::lean_dec(v_ctorIdx_1292_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Created_elim___redArg(
    mut v_Created_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_Created_1298_);
    return v_Created_1298_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Created_elim___redArg___boxed(
    mut v_Created_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Lean_Lsp_FileChangeType_Created_elim___redArg(v_Created_1299_);
    crate::leanh::lean_dec(v_Created_1299_);
    return v_res_1300_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Created_elim(
    mut v_motive_1301_: *mut crate::leanh::LeanObject,
    mut v_t_1302_: u8,
    mut v_h_1303_: *mut crate::leanh::LeanObject,
    mut v_Created_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_Created_1304_);
    return v_Created_1304_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Created_elim___boxed(
    mut v_motive_1305_: *mut crate::leanh::LeanObject,
    mut v_t_1306_: *mut crate::leanh::LeanObject,
    mut v_h_1307_: *mut crate::leanh::LeanObject,
    mut v_Created_1308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1309_: u8 = 0;
    let mut v_res_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1309_ = (crate::leanh::lean_unbox(v_t_1306_) as u8);
    v_res_1310_ = l_Lean_Lsp_FileChangeType_Created_elim(
        v_motive_1305_,
        v_t_boxed_1309_,
        v_h_1307_,
        v_Created_1308_,
    );
    crate::leanh::lean_dec(v_Created_1308_);
    return v_res_1310_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Changed_elim___redArg(
    mut v_Changed_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_Changed_1311_);
    return v_Changed_1311_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Changed_elim___redArg___boxed(
    mut v_Changed_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_Lean_Lsp_FileChangeType_Changed_elim___redArg(v_Changed_1312_);
    crate::leanh::lean_dec(v_Changed_1312_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Changed_elim(
    mut v_motive_1314_: *mut crate::leanh::LeanObject,
    mut v_t_1315_: u8,
    mut v_h_1316_: *mut crate::leanh::LeanObject,
    mut v_Changed_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_Changed_1317_);
    return v_Changed_1317_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Changed_elim___boxed(
    mut v_motive_1318_: *mut crate::leanh::LeanObject,
    mut v_t_1319_: *mut crate::leanh::LeanObject,
    mut v_h_1320_: *mut crate::leanh::LeanObject,
    mut v_Changed_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1322_: u8 = 0;
    let mut v_res_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1322_ = (crate::leanh::lean_unbox(v_t_1319_) as u8);
    v_res_1323_ = l_Lean_Lsp_FileChangeType_Changed_elim(
        v_motive_1318_,
        v_t_boxed_1322_,
        v_h_1320_,
        v_Changed_1321_,
    );
    crate::leanh::lean_dec(v_Changed_1321_);
    return v_res_1323_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(
    mut v_Deleted_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_Deleted_1324_);
    return v_Deleted_1324_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Deleted_elim___redArg___boxed(
    mut v_Deleted_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1326_ = l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(v_Deleted_1325_);
    crate::leanh::lean_dec(v_Deleted_1325_);
    return v_res_1326_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Deleted_elim(
    mut v_motive_1327_: *mut crate::leanh::LeanObject,
    mut v_t_1328_: u8,
    mut v_h_1329_: *mut crate::leanh::LeanObject,
    mut v_Deleted_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_Deleted_1330_);
    return v_Deleted_1330_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Deleted_elim___boxed(
    mut v_motive_1331_: *mut crate::leanh::LeanObject,
    mut v_t_1332_: *mut crate::leanh::LeanObject,
    mut v_h_1333_: *mut crate::leanh::LeanObject,
    mut v_Deleted_1334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1335_: u8 = 0;
    let mut v_res_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1335_ = (crate::leanh::lean_unbox(v_t_1332_) as u8);
    v_res_1336_ = l_Lean_Lsp_FileChangeType_Deleted_elim(
        v_motive_1331_,
        v_t_boxed_1335_,
        v_h_1333_,
        v_Deleted_1334_,
    );
    crate::leanh::lean_dec(v_Deleted_1334_);
    return v_res_1336_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonFileChangeType___lam__0(
    mut v_j_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1352_: u8 = 0;
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1356_: u8 = 0;
    let mut v_a_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1360_: u8 = 0;
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: u8 = 0;
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_j_1347_);
                v___x_1348_ = l_Lean_Json_getNat_x3f(v_j_1347_);
                if crate::leanh::lean_obj_tag(v___x_1348_) == 0 {
                    crate::leanh::lean_dec(v_j_1347_);
                    v_a_1349_ = crate::leanh::lean_ctor_get(v___x_1348_, 0);
                    v_isSharedCheck_1356_ = (!crate::leanh::lean_is_exclusive(v___x_1348_)) as u8;
                    if v_isSharedCheck_1356_ == 0 {
                        v___x_1351_ = v___x_1348_;
                        v_isShared_1352_ = v_isSharedCheck_1356_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1349_);
                        crate::leanh::lean_dec(v___x_1348_);
                        v___x_1351_ = crate::leanh::lean_box(0);
                        v_isShared_1352_ = v_isSharedCheck_1356_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1357_ = crate::leanh::lean_ctor_get(v___x_1348_, 0);
                    v_isSharedCheck_1377_ = (!crate::leanh::lean_is_exclusive(v___x_1348_)) as u8;
                    if v_isSharedCheck_1377_ == 0 {
                        v___x_1359_ = v___x_1348_;
                        v_isShared_1360_ = v_isSharedCheck_1377_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1357_);
                        crate::leanh::lean_dec(v___x_1348_);
                        v___x_1359_ = crate::leanh::lean_box(0);
                        v_isShared_1360_ = v_isSharedCheck_1377_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1352_ == 0 {
                    v___x_1354_ = v___x_1351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
                    v___x_1354_ = v_reuseFailAlloc_1355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1354_;
            }
            3 => {
                v___x_1361_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1362_ = lean_nat_dec_eq(v_a_1357_, v___x_1361_);
                if v___x_1362_ == 0 {
                    v___x_1363_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1364_ = lean_nat_dec_eq(v_a_1357_, v___x_1363_);
                    if v___x_1364_ == 0 {
                        v___x_1365_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_1366_ = lean_nat_dec_eq(v_a_1357_, v___x_1365_);
                        crate::leanh::lean_dec(v_a_1357_);
                        if v___x_1366_ == 0 {
                            v___x_1367_ =
                                l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0;
                            v___x_1368_ = crate::leanh::lean_unsigned_to_nat(80);
                            v___x_1369_ = l_Lean_Json_pretty(v_j_1347_, v___x_1368_);
                            v___x_1370_ = lean_string_append(v___x_1367_, v___x_1369_);
                            crate::leanh::lean_dec_ref(v___x_1369_);
                            if v_isShared_1360_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_1359_, 0);
                                crate::leanh::lean_ctor_set(v___x_1359_, 0, v___x_1370_);
                                v___x_1372_ = v___x_1359_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1373_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
                                v___x_1372_ = v_reuseFailAlloc_1373_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1359_);
                            crate::leanh::lean_dec(v_j_1347_);
                            v___x_1374_ =
                                l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1;
                            return v___x_1374_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1359_);
                        crate::leanh::lean_dec(v_a_1357_);
                        crate::leanh::lean_dec(v_j_1347_);
                        v___x_1375_ = l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2;
                        return v___x_1375_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1359_);
                    crate::leanh::lean_dec(v_a_1357_);
                    crate::leanh::lean_dec(v_j_1347_);
                    v___x_1376_ = l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3;
                    return v___x_1376_;
                }
            }
            4 => {
                return v___x_1372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1381_ = l_Lean_JsonNumber_fromNat(v___x_1380_);
    return v___x_1381_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1382_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0_once),
        _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0,
    );
    v___x_1383_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1383_, 0, v___x_1382_);
    return v___x_1383_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1385_ = l_Lean_JsonNumber_fromNat(v___x_1384_);
    return v___x_1385_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2_once),
        _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2,
    );
    v___x_1387_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1387_, 0, v___x_1386_);
    return v___x_1387_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1389_ = l_Lean_JsonNumber_fromNat(v___x_1388_);
    return v___x_1389_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1390_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4_once),
        _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4,
    );
    v___x_1391_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1391_, 0, v___x_1390_);
    return v___x_1391_;
}
pub unsafe fn l_Lean_Lsp_instToJsonFileChangeType___lam__0(
    mut v_x_1392_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1392_ {
        0 => {
            let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1393_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once
                ),
                _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1,
            );
            return v___x_1393_;
        }
        1 => {
            let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1394_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once
                ),
                _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3,
            );
            return v___x_1394_;
        }
        _ => {
            let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1395_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once
                ),
                _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5,
            );
            return v___x_1395_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonFileChangeType___lam__0___boxed(
    mut v_x_1396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_102__boxed_1397_: u8 = 0;
    let mut v_res_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_102__boxed_1397_ = (crate::leanh::lean_unbox(v_x_1396_) as u8);
    v_res_1398_ = l_Lean_Lsp_instToJsonFileChangeType___lam__0(v_x_102__boxed_1397_);
    return v_res_1398_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(
    mut v_j_1401_: *mut crate::leanh::LeanObject,
    mut v_k_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1408_: u8 = 0;
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v_a_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: u8 = 0;
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1403_ = l_Lean_Json_getObjValD(v_j_1401_, v_k_1402_);
                crate::leanh::lean_inc(v___x_1403_);
                v___x_1404_ = l_Lean_Json_getNat_x3f(v___x_1403_);
                if crate::leanh::lean_obj_tag(v___x_1404_) == 0 {
                    crate::leanh::lean_dec(v___x_1403_);
                    v_a_1405_ = crate::leanh::lean_ctor_get(v___x_1404_, 0);
                    v_isSharedCheck_1412_ = (!crate::leanh::lean_is_exclusive(v___x_1404_)) as u8;
                    if v_isSharedCheck_1412_ == 0 {
                        v___x_1407_ = v___x_1404_;
                        v_isShared_1408_ = v_isSharedCheck_1412_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1405_);
                        crate::leanh::lean_dec(v___x_1404_);
                        v___x_1407_ = crate::leanh::lean_box(0);
                        v_isShared_1408_ = v_isSharedCheck_1412_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1413_ = crate::leanh::lean_ctor_get(v___x_1404_, 0);
                    v_isSharedCheck_1433_ = (!crate::leanh::lean_is_exclusive(v___x_1404_)) as u8;
                    if v_isSharedCheck_1433_ == 0 {
                        v___x_1415_ = v___x_1404_;
                        v_isShared_1416_ = v_isSharedCheck_1433_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1413_);
                        crate::leanh::lean_dec(v___x_1404_);
                        v___x_1415_ = crate::leanh::lean_box(0);
                        v_isShared_1416_ = v_isSharedCheck_1433_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1408_ == 0 {
                    v___x_1410_ = v___x_1407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
                    v___x_1410_ = v_reuseFailAlloc_1411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1410_;
            }
            3 => {
                v___x_1417_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1418_ = lean_nat_dec_eq(v_a_1413_, v___x_1417_);
                if v___x_1418_ == 0 {
                    v___x_1419_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1420_ = lean_nat_dec_eq(v_a_1413_, v___x_1419_);
                    if v___x_1420_ == 0 {
                        v___x_1421_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_1422_ = lean_nat_dec_eq(v_a_1413_, v___x_1421_);
                        crate::leanh::lean_dec(v_a_1413_);
                        if v___x_1422_ == 0 {
                            v___x_1423_ =
                                l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0;
                            v___x_1424_ = crate::leanh::lean_unsigned_to_nat(80);
                            v___x_1425_ = l_Lean_Json_pretty(v___x_1403_, v___x_1424_);
                            v___x_1426_ = lean_string_append(v___x_1423_, v___x_1425_);
                            crate::leanh::lean_dec_ref(v___x_1425_);
                            if v_isShared_1416_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_1415_, 0);
                                crate::leanh::lean_ctor_set(v___x_1415_, 0, v___x_1426_);
                                v___x_1428_ = v___x_1415_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1429_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
                                v___x_1428_ = v_reuseFailAlloc_1429_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1415_);
                            crate::leanh::lean_dec(v___x_1403_);
                            v___x_1430_ =
                                l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1;
                            return v___x_1430_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1415_);
                        crate::leanh::lean_dec(v_a_1413_);
                        crate::leanh::lean_dec(v___x_1403_);
                        v___x_1431_ = l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2;
                        return v___x_1431_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1415_);
                    crate::leanh::lean_dec(v_a_1413_);
                    crate::leanh::lean_dec(v___x_1403_);
                    v___x_1432_ = l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3;
                    return v___x_1432_;
                }
            }
            4 => {
                return v___x_1428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0___boxed(
    mut v_j_1434_: *mut crate::leanh::LeanObject,
    mut v_k_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1436_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(
            v_j_1434_, v_k_1435_,
        );
    crate::leanh::lean_dec_ref(v_k_1435_);
    return v_res_1436_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = 1;
    v___x_1443_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1;
    v___x_1444_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1443_, v___x_1442_);
    return v___x_1444_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1445_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5;
    v___x_1446_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2,
    );
    v___x_1447_ = lean_string_append(v___x_1446_, v___x_1445_);
    return v___x_1447_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8,
    );
    v___x_1449_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3,
    );
    v___x_1450_ = lean_string_append(v___x_1449_, v___x_1448_);
    return v___x_1450_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1451_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1452_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4,
    );
    v___x_1453_ = lean_string_append(v___x_1452_, v___x_1451_);
    return v___x_1453_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1457_: u8 = 0;
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = 1;
    v___x_1458_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7;
    v___x_1459_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1458_, v___x_1457_);
    return v___x_1459_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8,
    );
    v___x_1461_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3,
    );
    v___x_1462_ = lean_string_append(v___x_1461_, v___x_1460_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1464_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9,
    );
    v___x_1465_ = lean_string_append(v___x_1464_, v___x_1463_);
    return v___x_1465_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonFileEvent_fromJson(
    mut v_json_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1472_: u8 = 0;
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1478_: u8 = 0;
    let mut v_a_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1482_: u8 = 0;
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v_a_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1499_: u8 = 0;
    let mut v_a_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1503_: u8 = 0;
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_a_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1511_: u8 = 0;
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1467_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0;
                crate::leanh::lean_inc(v_json_1466_);
                v___x_1468_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_1466_, v___x_1467_);
                if crate::leanh::lean_obj_tag(v___x_1468_) == 0 {
                    crate::leanh::lean_dec(v_json_1466_);
                    v_a_1469_ = crate::leanh::lean_ctor_get(v___x_1468_, 0);
                    v_isSharedCheck_1478_ = (!crate::leanh::lean_is_exclusive(v___x_1468_)) as u8;
                    if v_isSharedCheck_1478_ == 0 {
                        v___x_1471_ = v___x_1468_;
                        v_isShared_1472_ = v_isSharedCheck_1478_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1469_);
                        crate::leanh::lean_dec(v___x_1468_);
                        v___x_1471_ = crate::leanh::lean_box(0);
                        v_isShared_1472_ = v_isSharedCheck_1478_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_1468_) == 0 {
                        crate::leanh::lean_dec(v_json_1466_);
                        v_a_1479_ = crate::leanh::lean_ctor_get(v___x_1468_, 0);
                        v_isSharedCheck_1486_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1468_)) as u8;
                        if v_isSharedCheck_1486_ == 0 {
                            v___x_1481_ = v___x_1468_;
                            v_isShared_1482_ = v_isSharedCheck_1486_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1479_);
                            crate::leanh::lean_dec(v___x_1468_);
                            v___x_1481_ = crate::leanh::lean_box(0);
                            v_isShared_1482_ = v_isSharedCheck_1486_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1487_ = crate::leanh::lean_ctor_get(v___x_1468_, 0);
                        crate::leanh::lean_inc(v_a_1487_);
                        crate::leanh::lean_dec_ref_known(v___x_1468_, 1);
                        v___x_1488_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6;
                        v___x_1489_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(v_json_1466_, v___x_1488_);
                        if crate::leanh::lean_obj_tag(v___x_1489_) == 0 {
                            crate::leanh::lean_dec(v_a_1487_);
                            v_a_1490_ = crate::leanh::lean_ctor_get(v___x_1489_, 0);
                            v_isSharedCheck_1499_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1489_)) as u8;
                            if v_isSharedCheck_1499_ == 0 {
                                v___x_1492_ = v___x_1489_;
                                v_isShared_1493_ = v_isSharedCheck_1499_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1490_);
                                crate::leanh::lean_dec(v___x_1489_);
                                v___x_1492_ = crate::leanh::lean_box(0);
                                v_isShared_1493_ = v_isSharedCheck_1499_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_1489_) == 0 {
                                crate::leanh::lean_dec(v_a_1487_);
                                v_a_1500_ = crate::leanh::lean_ctor_get(v___x_1489_, 0);
                                v_isSharedCheck_1507_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1489_)) as u8;
                                if v_isSharedCheck_1507_ == 0 {
                                    v___x_1502_ = v___x_1489_;
                                    v_isShared_1503_ = v_isSharedCheck_1507_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1500_);
                                    crate::leanh::lean_dec(v___x_1489_);
                                    v___x_1502_ = crate::leanh::lean_box(0);
                                    v_isShared_1503_ = v_isSharedCheck_1507_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_1508_ = crate::leanh::lean_ctor_get(v___x_1489_, 0);
                                v_isSharedCheck_1517_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1489_)) as u8;
                                if v_isSharedCheck_1517_ == 0 {
                                    v___x_1510_ = v___x_1489_;
                                    v_isShared_1511_ = v_isSharedCheck_1517_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1508_);
                                    crate::leanh::lean_dec(v___x_1489_);
                                    v___x_1510_ = crate::leanh::lean_box(0);
                                    v_isShared_1511_ = v_isSharedCheck_1517_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1473_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5,
                );
                v___x_1474_ = lean_string_append(v___x_1473_, v_a_1469_);
                crate::leanh::lean_dec(v_a_1469_);
                if v_isShared_1472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1471_, 0, v___x_1474_);
                    v___x_1476_ = v___x_1471_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
                    v___x_1476_ = v_reuseFailAlloc_1477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1476_;
            }
            3 => {
                if v_isShared_1482_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1481_, 0);
                    v___x_1484_ = v___x_1481_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
                    v___x_1484_ = v_reuseFailAlloc_1485_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1484_;
            }
            5 => {
                v___x_1494_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10,
                );
                v___x_1495_ = lean_string_append(v___x_1494_, v_a_1490_);
                crate::leanh::lean_dec(v_a_1490_);
                if v_isShared_1493_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1492_, 0, v___x_1495_);
                    v___x_1497_ = v___x_1492_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
                    v___x_1497_ = v_reuseFailAlloc_1498_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1497_;
            }
            7 => {
                if v_isShared_1503_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1502_, 0);
                    v___x_1505_ = v___x_1502_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1506_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
                    v___x_1505_ = v_reuseFailAlloc_1506_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1505_;
            }
            9 => {
                v___x_1512_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1512_, 0, v_a_1487_);
                v___x_1513_ = (crate::leanh::lean_unbox(v_a_1508_) as u8);
                crate::leanh::lean_dec(v_a_1508_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1512_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1513_,
                );
                if v_isShared_1511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1512_);
                    v___x_1515_ = v___x_1510_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1516_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1512_);
                    v___x_1515_ = v_reuseFailAlloc_1516_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonFileEvent_toJson(
    mut v_x_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1522_: u8 = 0;
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_1521_ = crate::leanh::lean_ctor_get(v_x_1520_, 0);
                v_type_1522_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_1520_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_1523_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0;
                crate::leanh::lean_inc_ref(v_uri_1521_);
                v___x_1524_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1524_, 0, v_uri_1521_);
                v___x_1525_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1525_, 0, v___x_1523_);
                crate::leanh::lean_ctor_set(v___x_1525_, 1, v___x_1524_);
                v___x_1526_ = crate::leanh::lean_box(0);
                v___x_1527_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1527_, 0, v___x_1525_);
                crate::leanh::lean_ctor_set(v___x_1527_, 1, v___x_1526_);
                v___x_1528_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6;
                match v_type_1522_ {
                    0 => {
                        v___x_1538_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1,
                        );
                        v___y_1530_ = v___x_1538_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_1539_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3,
                        );
                        v___y_1530_ = v___x_1539_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1540_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once
                            ),
                            _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5,
                        );
                        v___y_1530_ = v___x_1540_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_1530_);
                v___x_1531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1531_, 0, v___x_1528_);
                crate::leanh::lean_ctor_set(v___x_1531_, 1, v___y_1530_);
                v___x_1532_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1532_, 0, v___x_1531_);
                crate::leanh::lean_ctor_set(v___x_1532_, 1, v___x_1526_);
                v___x_1533_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1533_, 0, v___x_1532_);
                crate::leanh::lean_ctor_set(v___x_1533_, 1, v___x_1526_);
                v___x_1534_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1534_, 0, v___x_1527_);
                crate::leanh::lean_ctor_set(v___x_1534_, 1, v___x_1533_);
                v___x_1535_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2;
                v___x_1536_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_1534_, v___x_1535_);
                v___x_1537_ = l_Lean_Json_mkObj(v___x_1536_);
                crate::leanh::lean_dec(v___x_1536_);
                return v___x_1537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonFileEvent_toJson___boxed(
    mut v_x_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Lean_Lsp_instToJsonFileEvent_toJson(v_x_1541_);
    crate::leanh::lean_dec_ref(v_x_1541_);
    return v_res_1542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(
    mut v_sz_1545_: usize,
    mut v_i_1546_: usize,
    mut v_bs_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1548_: u8 = 0;
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut v_a_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: usize = 0;
    let mut v___x_1564_: usize = 0;
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1548_ = lean_usize_dec_lt(v_i_1546_, v_sz_1545_);
                if v___x_1548_ == 0 {
                    v___x_1549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1549_, 0, v_bs_1547_);
                    return v___x_1549_;
                } else {
                    v_v_1550_ = lean_array_uget_borrowed(v_bs_1547_, v_i_1546_);
                    crate::leanh::lean_inc(v_v_1550_);
                    v___x_1551_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson(v_v_1550_);
                    if crate::leanh::lean_obj_tag(v___x_1551_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_1547_);
                        v_a_1552_ = crate::leanh::lean_ctor_get(v___x_1551_, 0);
                        v_isSharedCheck_1559_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1551_)) as u8;
                        if v_isSharedCheck_1559_ == 0 {
                            v___x_1554_ = v___x_1551_;
                            v_isShared_1555_ = v_isSharedCheck_1559_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1552_);
                            crate::leanh::lean_dec(v___x_1551_);
                            v___x_1554_ = crate::leanh::lean_box(0);
                            v_isShared_1555_ = v_isSharedCheck_1559_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1560_ = crate::leanh::lean_ctor_get(v___x_1551_, 0);
                        crate::leanh::lean_inc(v_a_1560_);
                        crate::leanh::lean_dec_ref_known(v___x_1551_, 1);
                        v___x_1561_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1562_ = lean_array_uset(v_bs_1547_, v_i_1546_, v___x_1561_);
                        v___x_1563_ = 1usize;
                        v___x_1564_ = lean_usize_add(v_i_1546_, v___x_1563_);
                        v___x_1565_ = lean_array_uset(v_bs_x27_1562_, v_i_1546_, v_a_1560_);
                        v_i_1546_ = v___x_1564_;
                        v_bs_1547_ = v___x_1565_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1555_ == 0 {
                    v___x_1557_ = v___x_1554_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
                    v___x_1557_ = v_reuseFailAlloc_1558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1___boxed(
    mut v_sz_1567_: *mut crate::leanh::LeanObject,
    mut v_i_1568_: *mut crate::leanh::LeanObject,
    mut v_bs_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1570_: usize = 0;
    let mut v_i_boxed_1571_: usize = 0;
    let mut v_res_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1570_ = crate::leanh::lean_unbox_usize(v_sz_1567_);
    crate::leanh::lean_dec(v_sz_1567_);
    v_i_boxed_1571_ = crate::leanh::lean_unbox_usize(v_i_1568_);
    crate::leanh::lean_dec(v_i_1568_);
    v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1570_, v_i_boxed_1571_, v_bs_1569_);
    return v_res_1572_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(
    mut v_x_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1573_) == 4 {
        let mut v_elems_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1575_: usize = 0;
        let mut v___x_1576_: usize = 0;
        let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_1574_ = crate::leanh::lean_ctor_get(v_x_1573_, 0);
        crate::leanh::lean_inc_ref(v_elems_1574_);
        crate::leanh::lean_dec_ref_known(v_x_1573_, 1);
        v_sz_1575_ = lean_array_size(v_elems_1574_);
        v___x_1576_ = 0usize;
        v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_1575_, v___x_1576_, v_elems_1574_);
        return v___x_1577_;
    } else {
        let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1578_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0;
        v___x_1579_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_1580_ = l_Lean_Json_pretty(v_x_1573_, v___x_1579_);
        v___x_1581_ = lean_string_append(v___x_1578_, v___x_1580_);
        crate::leanh::lean_dec_ref(v___x_1580_);
        v___x_1582_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1;
        v___x_1583_ = lean_string_append(v___x_1581_, v___x_1582_);
        v___x_1584_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1584_, 0, v___x_1583_);
        return v___x_1584_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(
    mut v_j_1585_: *mut crate::leanh::LeanObject,
    mut v_k_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ = l_Lean_Json_getObjValD(v_j_1585_, v_k_1586_);
    v___x_1588_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(v___x_1587_);
    return v___x_1588_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0___boxed(
    mut v_j_1589_: *mut crate::leanh::LeanObject,
    mut v_k_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1591_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(v_j_1589_, v_k_1590_);
    crate::leanh::lean_dec_ref(v_k_1590_);
    return v_res_1591_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = 1;
    v___x_1599_ = l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2;
    v___x_1600_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1599_, v___x_1598_);
    return v___x_1600_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1601_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5;
    v___x_1602_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3,
    );
    v___x_1603_ = lean_string_append(v___x_1602_, v___x_1601_);
    return v___x_1603_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: u8 = 0;
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = 1;
    v___x_1607_ = l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5;
    v___x_1608_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1607_, v___x_1606_);
    return v___x_1608_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6,
    );
    v___x_1610_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4,
    );
    v___x_1611_ = lean_string_append(v___x_1610_, v___x_1609_);
    return v___x_1611_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1612_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1613_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7,
    );
    v___x_1614_ = lean_string_append(v___x_1613_, v___x_1612_);
    return v___x_1614_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson(
    mut v_json_1615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut v_a_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_a_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1616_ =
                    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0;
                v___x_1617_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(v_json_1615_, v___x_1616_);
                if crate::leanh::lean_obj_tag(v___x_1617_) == 0 {
                    v_a_1618_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                    v_isSharedCheck_1627_ = (!crate::leanh::lean_is_exclusive(v___x_1617_)) as u8;
                    if v_isSharedCheck_1627_ == 0 {
                        v___x_1620_ = v___x_1617_;
                        v_isShared_1621_ = v_isSharedCheck_1627_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1618_);
                        crate::leanh::lean_dec(v___x_1617_);
                        v___x_1620_ = crate::leanh::lean_box(0);
                        v_isShared_1621_ = v_isSharedCheck_1627_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_1617_) == 0 {
                        v_a_1628_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                        v_isSharedCheck_1635_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1617_)) as u8;
                        if v_isSharedCheck_1635_ == 0 {
                            v___x_1630_ = v___x_1617_;
                            v_isShared_1631_ = v_isSharedCheck_1635_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1628_);
                            crate::leanh::lean_dec(v___x_1617_);
                            v___x_1630_ = crate::leanh::lean_box(0);
                            v_isShared_1631_ = v_isSharedCheck_1635_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1636_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                        v_isSharedCheck_1643_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1617_)) as u8;
                        if v_isSharedCheck_1643_ == 0 {
                            v___x_1638_ = v___x_1617_;
                            v_isShared_1639_ = v_isSharedCheck_1643_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1636_);
                            crate::leanh::lean_dec(v___x_1617_);
                            v___x_1638_ = crate::leanh::lean_box(0);
                            v_isShared_1639_ = v_isSharedCheck_1643_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1622_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8);
                v___x_1623_ = lean_string_append(v___x_1622_, v_a_1618_);
                crate::leanh::lean_dec(v_a_1618_);
                if v_isShared_1621_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1620_, 0, v___x_1623_);
                    v___x_1625_ = v___x_1620_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
                    v___x_1625_ = v_reuseFailAlloc_1626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1625_;
            }
            3 => {
                if v_isShared_1631_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1630_, 0);
                    v___x_1633_ = v___x_1630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1633_;
            }
            5 => {
                if v_isShared_1639_ == 0 {
                    v___x_1641_ = v___x_1638_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(
    mut v_sz_1646_: usize,
    mut v_i_1647_: usize,
    mut v_bs_1648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1649_: u8 = 0;
    let mut v_v_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: usize = 0;
    let mut v___x_1655_: usize = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1649_ = lean_usize_dec_lt(v_i_1647_, v_sz_1646_);
                if v___x_1649_ == 0 {
                    return v_bs_1648_;
                } else {
                    v_v_1650_ = lean_array_uget(v_bs_1648_, v_i_1647_);
                    v___x_1651_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1652_ = lean_array_uset(v_bs_1648_, v_i_1647_, v___x_1651_);
                    v___x_1653_ = l_Lean_Lsp_instToJsonFileEvent_toJson(v_v_1650_);
                    crate::leanh::lean_dec(v_v_1650_);
                    v___x_1654_ = 1usize;
                    v___x_1655_ = lean_usize_add(v_i_1647_, v___x_1654_);
                    v___x_1656_ = lean_array_uset(v_bs_x27_1652_, v_i_1647_, v___x_1653_);
                    v_i_1647_ = v___x_1655_;
                    v_bs_1648_ = v___x_1656_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0___boxed(
    mut v_sz_1658_: *mut crate::leanh::LeanObject,
    mut v_i_1659_: *mut crate::leanh::LeanObject,
    mut v_bs_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1661_: usize = 0;
    let mut v_i_boxed_1662_: usize = 0;
    let mut v_res_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1661_ = crate::leanh::lean_unbox_usize(v_sz_1658_);
    crate::leanh::lean_dec(v_sz_1658_);
    v_i_boxed_1662_ = crate::leanh::lean_unbox_usize(v_i_1659_);
    crate::leanh::lean_dec(v_i_1659_);
    v_res_1663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_boxed_1661_, v_i_boxed_1662_, v_bs_1660_);
    return v_res_1663_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(
    mut v_a_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1665_: usize = 0;
    let mut v___x_1666_: usize = 0;
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_1665_ = lean_array_size(v_a_1664_);
    v___x_1666_ = 0usize;
    v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_1665_, v___x_1666_, v_a_1664_);
    v___x_1668_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1668_, 0, v___x_1667_);
    return v___x_1668_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson(
    mut v_x_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ = l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0;
    v___x_1671_ =
        l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(
            v_x_1669_,
        );
    v___x_1672_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1672_, 0, v___x_1670_);
    crate::leanh::lean_ctor_set(v___x_1672_, 1, v___x_1671_);
    v___x_1673_ = crate::leanh::lean_box(0);
    v___x_1674_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1674_, 0, v___x_1672_);
    crate::leanh::lean_ctor_set(v___x_1674_, 1, v___x_1673_);
    v___x_1675_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1675_, 0, v___x_1674_);
    crate::leanh::lean_ctor_set(v___x_1675_, 1, v___x_1673_);
    v___x_1676_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2;
    v___x_1677_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_1675_, v___x_1676_);
    v___x_1678_ = l_Lean_Json_mkObj(v___x_1677_);
    crate::leanh::lean_dec(v___x_1677_);
    return v___x_1678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Workspace(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Lsp_FileSystemWatcher_create = _init_l_Lean_Lsp_FileSystemWatcher_create();
    crate::leanh::lean_mark_persistent(l_Lean_Lsp_FileSystemWatcher_create);
    l_Lean_Lsp_FileSystemWatcher_change = _init_l_Lean_Lsp_FileSystemWatcher_change();
    crate::leanh::lean_mark_persistent(l_Lean_Lsp_FileSystemWatcher_change);
    l_Lean_Lsp_FileSystemWatcher_delete = _init_l_Lean_Lsp_FileSystemWatcher_delete();
    crate::leanh::lean_mark_persistent(l_Lean_Lsp_FileSystemWatcher_delete);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Workspace(
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
pub unsafe fn initialize_Lean_Data_Lsp_Workspace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Workspace(builtin);
}

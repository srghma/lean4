// Lean compiler output
// Module: Lean.Data.Lsp.Client
// Imports: Lean.Data.Lsp.Basic
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::Basic::{
    initialize_Lean_Data_Lsp_Basic, runtime_initialize_Lean_Data_Lsp_Basic,
};
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_string_append;
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::lean_array_to_list;
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value:
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
    m_data: [105, 100, 0],
};
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value:
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
    m_data: [109, 101, 116, 104, 111, 100, 0],
};
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__2_value:
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
        114, 101, 103, 105, 115, 116, 101, 114, 79, 112, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__3_value:
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
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRegistration_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRegistration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonRegistration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value:
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value:
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value:
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
    m_data: [82, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
        9349648586579053191 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5_value:
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6041859491766292191 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10_value:
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        10404875796858280754 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instFromJsonRegistration_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonRegistration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRegistration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
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
        114, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonRegistrationParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonRegistrationParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonRegistrationParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        82, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17292097268730655621 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3463206859181389405 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonRegistrationParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRegistrationParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(
    mut v_x_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_296_) == 0 {
        let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_297_ = crate::leanh::lean_box(0);
        return v___x_297_;
    } else {
        let mut v_val_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_298_ = crate::leanh::lean_ctor_get(v_x_296_, 0);
        crate::leanh::lean_inc(v_val_298_);
        return v_val_298_;
    }
}
pub unsafe fn l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0___boxed(
    mut v_x_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(v_x_299_);
    crate::leanh::lean_dec(v_x_299_);
    return v_res_300_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(
    mut v_a_301_: *mut crate::leanh::LeanObject,
    mut v_a_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_301_) == 0 {
                    v___x_303_ = lean_array_to_list(v_a_302_);
                    return v___x_303_;
                } else {
                    v_head_304_ = crate::leanh::lean_ctor_get(v_a_301_, 0);
                    crate::leanh::lean_inc(v_head_304_);
                    v_tail_305_ = crate::leanh::lean_ctor_get(v_a_301_, 1);
                    crate::leanh::lean_inc(v_tail_305_);
                    crate::leanh::lean_dec_ref_known(v_a_301_, 2);
                    v___x_306_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_302_,
                        v_head_304_,
                    );
                    v_a_301_ = v_tail_305_;
                    v_a_302_ = v___x_306_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonRegistration_toJson(
    mut v_x_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_registerOptions_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_id_314_ = crate::leanh::lean_ctor_get(v_x_313_, 0);
    v_method_315_ = crate::leanh::lean_ctor_get(v_x_313_, 1);
    v_registerOptions_316_ = crate::leanh::lean_ctor_get(v_x_313_, 2);
    v___x_317_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__0;
    crate::leanh::lean_inc_ref(v_id_314_);
    v___x_318_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_318_, 0, v_id_314_);
    v___x_319_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_319_, 0, v___x_317_);
    crate::leanh::lean_ctor_set(v___x_319_, 1, v___x_318_);
    v___x_320_ = crate::leanh::lean_box(0);
    v___x_321_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_321_, 0, v___x_319_);
    crate::leanh::lean_ctor_set(v___x_321_, 1, v___x_320_);
    v___x_322_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__1;
    crate::leanh::lean_inc_ref(v_method_315_);
    v___x_323_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_323_, 0, v_method_315_);
    v___x_324_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_324_, 0, v___x_322_);
    crate::leanh::lean_ctor_set(v___x_324_, 1, v___x_323_);
    v___x_325_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_325_, 0, v___x_324_);
    crate::leanh::lean_ctor_set(v___x_325_, 1, v___x_320_);
    v___x_326_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__2;
    v___x_327_ = l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(
        v_registerOptions_316_,
    );
    v___x_328_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_328_, 0, v___x_326_);
    crate::leanh::lean_ctor_set(v___x_328_, 1, v___x_327_);
    v___x_329_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_329_, 0, v___x_328_);
    crate::leanh::lean_ctor_set(v___x_329_, 1, v___x_320_);
    v___x_330_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_330_, 0, v___x_329_);
    crate::leanh::lean_ctor_set(v___x_330_, 1, v___x_320_);
    v___x_331_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_331_, 0, v___x_325_);
    crate::leanh::lean_ctor_set(v___x_331_, 1, v___x_330_);
    v___x_332_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_332_, 0, v___x_321_);
    crate::leanh::lean_ctor_set(v___x_332_, 1, v___x_331_);
    v___x_333_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__3;
    v___x_334_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(v___x_332_, v___x_333_);
    v___x_335_ = l_Lean_Json_mkObj(v___x_334_);
    crate::leanh::lean_dec(v___x_334_);
    return v___x_335_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRegistration_toJson___boxed(
    mut v_x_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Lean_Lsp_instToJsonRegistration_toJson(v_x_336_);
    crate::leanh::lean_dec_ref(v_x_336_);
    return v_res_337_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(
    mut v_j_340_: *mut crate::leanh::LeanObject,
    mut v_k_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Json_getObjValD(v_j_340_, v_k_341_);
    v___x_343_ = l_Lean_Json_getStr_x3f(v___x_342_);
    return v___x_343_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0___boxed(
    mut v_j_344_: *mut crate::leanh::LeanObject,
    mut v_k_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(
            v_j_344_, v_k_345_,
        );
    crate::leanh::lean_dec_ref(v_k_345_);
    return v_res_346_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(
    mut v_x_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_349_) == 0 {
        let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_350_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0;
        return v___x_350_;
    } else {
        let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_351_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_351_, 0, v_x_349_);
        v___x_352_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_352_, 0, v___x_351_);
        return v___x_352_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(
    mut v_j_353_: *mut crate::leanh::LeanObject,
    mut v_k_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = l_Lean_Json_getObjValD(v_j_353_, v_k_354_);
    v___x_356_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(v___x_355_);
    return v___x_356_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1___boxed(
    mut v_j_357_: *mut crate::leanh::LeanObject,
    mut v_k_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_359_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(
            v_j_357_, v_k_358_,
        );
    crate::leanh::lean_dec_ref(v_k_358_);
    return v_res_359_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_367_: u8 = 0;
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_367_ = 1;
    v___x_368_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3;
    v___x_369_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_368_, v___x_367_);
    return v___x_369_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5;
    v___x_372_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4,
    );
    v___x_373_ = lean_string_append(v___x_372_, v___x_371_);
    return v___x_373_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_376_: u8 = 0;
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = 1;
    v___x_377_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7;
    v___x_378_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_377_, v___x_376_);
    return v___x_378_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8,
    );
    v___x_380_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6,
    );
    v___x_381_ = lean_string_append(v___x_380_, v___x_379_);
    return v___x_381_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10;
    v___x_384_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9,
    );
    v___x_385_ = lean_string_append(v___x_384_, v___x_383_);
    return v___x_385_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_388_: u8 = 0;
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = 1;
    v___x_389_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12;
    v___x_390_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_389_, v___x_388_);
    return v___x_390_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13,
    );
    v___x_392_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6,
    );
    v___x_393_ = lean_string_append(v___x_392_, v___x_391_);
    return v___x_393_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10;
    v___x_395_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14,
    );
    v___x_396_ = lean_string_append(v___x_395_, v___x_394_);
    return v___x_396_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRegistration_fromJson(
    mut v_json_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_403_: u8 = 0;
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_409_: u8 = 0;
    let mut v_a_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_413_: u8 = 0;
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_417_: u8 = 0;
    let mut v_a_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_424_: u8 = 0;
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v_a_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_434_: u8 = 0;
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_438_: u8 = 0;
    let mut v_a_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_445_: u8 = 0;
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_398_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__0;
                crate::leanh::lean_inc(v_json_397_);
                v___x_399_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(v_json_397_, v___x_398_);
                if crate::leanh::lean_obj_tag(v___x_399_) == 0 {
                    crate::leanh::lean_dec(v_json_397_);
                    v_a_400_ = crate::leanh::lean_ctor_get(v___x_399_, 0);
                    v_isSharedCheck_409_ = (!crate::leanh::lean_is_exclusive(v___x_399_)) as u8;
                    if v_isSharedCheck_409_ == 0 {
                        v___x_402_ = v___x_399_;
                        v_isShared_403_ = v_isSharedCheck_409_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_400_);
                        crate::leanh::lean_dec(v___x_399_);
                        v___x_402_ = crate::leanh::lean_box(0);
                        v_isShared_403_ = v_isSharedCheck_409_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_399_) == 0 {
                        crate::leanh::lean_dec(v_json_397_);
                        v_a_410_ = crate::leanh::lean_ctor_get(v___x_399_, 0);
                        v_isSharedCheck_417_ = (!crate::leanh::lean_is_exclusive(v___x_399_)) as u8;
                        if v_isSharedCheck_417_ == 0 {
                            v___x_412_ = v___x_399_;
                            v_isShared_413_ = v_isSharedCheck_417_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_410_);
                            crate::leanh::lean_dec(v___x_399_);
                            v___x_412_ = crate::leanh::lean_box(0);
                            v_isShared_413_ = v_isSharedCheck_417_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_418_ = crate::leanh::lean_ctor_get(v___x_399_, 0);
                        crate::leanh::lean_inc(v_a_418_);
                        crate::leanh::lean_dec_ref_known(v___x_399_, 1);
                        v___x_419_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__1;
                        crate::leanh::lean_inc(v_json_397_);
                        v___x_420_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(v_json_397_, v___x_419_);
                        if crate::leanh::lean_obj_tag(v___x_420_) == 0 {
                            crate::leanh::lean_dec(v_a_418_);
                            crate::leanh::lean_dec(v_json_397_);
                            v_a_421_ = crate::leanh::lean_ctor_get(v___x_420_, 0);
                            v_isSharedCheck_430_ =
                                (!crate::leanh::lean_is_exclusive(v___x_420_)) as u8;
                            if v_isSharedCheck_430_ == 0 {
                                v___x_423_ = v___x_420_;
                                v_isShared_424_ = v_isSharedCheck_430_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_421_);
                                crate::leanh::lean_dec(v___x_420_);
                                v___x_423_ = crate::leanh::lean_box(0);
                                v_isShared_424_ = v_isSharedCheck_430_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_420_) == 0 {
                                crate::leanh::lean_dec(v_a_418_);
                                crate::leanh::lean_dec(v_json_397_);
                                v_a_431_ = crate::leanh::lean_ctor_get(v___x_420_, 0);
                                v_isSharedCheck_438_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_420_)) as u8;
                                if v_isSharedCheck_438_ == 0 {
                                    v___x_433_ = v___x_420_;
                                    v_isShared_434_ = v_isSharedCheck_438_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_431_);
                                    crate::leanh::lean_dec(v___x_420_);
                                    v___x_433_ = crate::leanh::lean_box(0);
                                    v_isShared_434_ = v_isSharedCheck_438_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_439_ = crate::leanh::lean_ctor_get(v___x_420_, 0);
                                crate::leanh::lean_inc(v_a_439_);
                                crate::leanh::lean_dec_ref_known(v___x_420_, 1);
                                v___x_440_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__2;
                                v___x_441_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(v_json_397_, v___x_440_);
                                v_a_442_ = crate::leanh::lean_ctor_get(v___x_441_, 0);
                                v_isSharedCheck_450_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_441_)) as u8;
                                if v_isSharedCheck_450_ == 0 {
                                    v___x_444_ = v___x_441_;
                                    v_isShared_445_ = v_isSharedCheck_450_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_442_);
                                    crate::leanh::lean_dec(v___x_441_);
                                    v___x_444_ = crate::leanh::lean_box(0);
                                    v_isShared_445_ = v_isSharedCheck_450_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_404_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11,
                );
                v___x_405_ = lean_string_append(v___x_404_, v_a_400_);
                crate::leanh::lean_dec(v_a_400_);
                if v_isShared_403_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_402_, 0, v___x_405_);
                    v___x_407_ = v___x_402_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
                    v___x_407_ = v_reuseFailAlloc_408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_407_;
            }
            3 => {
                if v_isShared_413_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_412_, 0);
                    v___x_415_ = v___x_412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_416_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
                    v___x_415_ = v_reuseFailAlloc_416_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_415_;
            }
            5 => {
                v___x_425_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15,
                );
                v___x_426_ = lean_string_append(v___x_425_, v_a_421_);
                crate::leanh::lean_dec(v_a_421_);
                if v_isShared_424_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_423_, 0, v___x_426_);
                    v___x_428_ = v___x_423_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
                    v___x_428_ = v_reuseFailAlloc_429_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_428_;
            }
            7 => {
                if v_isShared_434_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_433_, 0);
                    v___x_436_ = v___x_433_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_437_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
                    v___x_436_ = v_reuseFailAlloc_437_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_436_;
            }
            9 => {
                v___x_446_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_446_, 0, v_a_418_);
                crate::leanh::lean_ctor_set(v___x_446_, 1, v_a_439_);
                crate::leanh::lean_ctor_set(v___x_446_, 2, v_a_442_);
                if v_isShared_445_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_444_, 0, v___x_446_);
                    v___x_448_ = v___x_444_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
                    v___x_448_ = v_reuseFailAlloc_449_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(
    mut v_sz_453_: usize,
    mut v_i_454_: usize,
    mut v_bs_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_456_: u8 = 0;
    let mut v_v_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: usize = 0;
    let mut v___x_462_: usize = 0;
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_456_ = lean_usize_dec_lt(v_i_454_, v_sz_453_);
                if v___x_456_ == 0 {
                    return v_bs_455_;
                } else {
                    v_v_457_ = lean_array_uget(v_bs_455_, v_i_454_);
                    v___x_458_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_459_ = lean_array_uset(v_bs_455_, v_i_454_, v___x_458_);
                    v___x_460_ = l_Lean_Lsp_instToJsonRegistration_toJson(v_v_457_);
                    crate::leanh::lean_dec(v_v_457_);
                    v___x_461_ = 1usize;
                    v___x_462_ = lean_usize_add(v_i_454_, v___x_461_);
                    v___x_463_ = lean_array_uset(v_bs_x27_459_, v_i_454_, v___x_460_);
                    v_i_454_ = v___x_462_;
                    v_bs_455_ = v___x_463_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0___boxed(
    mut v_sz_465_: *mut crate::leanh::LeanObject,
    mut v_i_466_: *mut crate::leanh::LeanObject,
    mut v_bs_467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_468_: usize = 0;
    let mut v_i_boxed_469_: usize = 0;
    let mut v_res_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_468_ = crate::leanh::lean_unbox_usize(v_sz_465_);
    crate::leanh::lean_dec(v_sz_465_);
    v_i_boxed_469_ = crate::leanh::lean_unbox_usize(v_i_466_);
    crate::leanh::lean_dec(v_i_466_);
    v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(v_sz_boxed_468_, v_i_boxed_469_, v_bs_467_);
    return v_res_470_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(
    mut v_a_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_472_: usize = 0;
    let mut v___x_473_: usize = 0;
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_472_ = lean_array_size(v_a_471_);
    v___x_473_ = 0usize;
    v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(v_sz_472_, v___x_473_, v_a_471_);
    v___x_475_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_475_, 0, v___x_474_);
    return v___x_475_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRegistrationParams_toJson(
    mut v_x_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_478_ = l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0;
    v___x_479_ =
        l_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(v_x_477_);
    v___x_480_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_480_, 0, v___x_478_);
    crate::leanh::lean_ctor_set(v___x_480_, 1, v___x_479_);
    v___x_481_ = crate::leanh::lean_box(0);
    v___x_482_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_482_, 0, v___x_480_);
    crate::leanh::lean_ctor_set(v___x_482_, 1, v___x_481_);
    v___x_483_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_483_, 0, v___x_482_);
    crate::leanh::lean_ctor_set(v___x_483_, 1, v___x_481_);
    v___x_484_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__3;
    v___x_485_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(v___x_483_, v___x_484_);
    v___x_486_ = l_Lean_Json_mkObj(v___x_485_);
    crate::leanh::lean_dec(v___x_485_);
    return v___x_486_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(
    mut v_sz_489_: usize,
    mut v_i_490_: usize,
    mut v_bs_491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_492_: u8 = 0;
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_499_: u8 = 0;
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_503_: u8 = 0;
    let mut v_a_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: usize = 0;
    let mut v___x_508_: usize = 0;
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_492_ = lean_usize_dec_lt(v_i_490_, v_sz_489_);
                if v___x_492_ == 0 {
                    v___x_493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_493_, 0, v_bs_491_);
                    return v___x_493_;
                } else {
                    v_v_494_ = lean_array_uget_borrowed(v_bs_491_, v_i_490_);
                    crate::leanh::lean_inc(v_v_494_);
                    v___x_495_ = l_Lean_Lsp_instFromJsonRegistration_fromJson(v_v_494_);
                    if crate::leanh::lean_obj_tag(v___x_495_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_491_);
                        v_a_496_ = crate::leanh::lean_ctor_get(v___x_495_, 0);
                        v_isSharedCheck_503_ = (!crate::leanh::lean_is_exclusive(v___x_495_)) as u8;
                        if v_isSharedCheck_503_ == 0 {
                            v___x_498_ = v___x_495_;
                            v_isShared_499_ = v_isSharedCheck_503_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_496_);
                            crate::leanh::lean_dec(v___x_495_);
                            v___x_498_ = crate::leanh::lean_box(0);
                            v_isShared_499_ = v_isSharedCheck_503_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_504_ = crate::leanh::lean_ctor_get(v___x_495_, 0);
                        crate::leanh::lean_inc(v_a_504_);
                        crate::leanh::lean_dec_ref_known(v___x_495_, 1);
                        v___x_505_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_506_ = lean_array_uset(v_bs_491_, v_i_490_, v___x_505_);
                        v___x_507_ = 1usize;
                        v___x_508_ = lean_usize_add(v_i_490_, v___x_507_);
                        v___x_509_ = lean_array_uset(v_bs_x27_506_, v_i_490_, v_a_504_);
                        v_i_490_ = v___x_508_;
                        v_bs_491_ = v___x_509_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_499_ == 0 {
                    v___x_501_ = v___x_498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
                    v___x_501_ = v_reuseFailAlloc_502_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1___boxed(
    mut v_sz_511_: *mut crate::leanh::LeanObject,
    mut v_i_512_: *mut crate::leanh::LeanObject,
    mut v_bs_513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_514_: usize = 0;
    let mut v_i_boxed_515_: usize = 0;
    let mut v_res_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_514_ = crate::leanh::lean_unbox_usize(v_sz_511_);
    crate::leanh::lean_dec(v_sz_511_);
    v_i_boxed_515_ = crate::leanh::lean_unbox_usize(v_i_512_);
    crate::leanh::lean_dec(v_i_512_);
    v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_514_, v_i_boxed_515_, v_bs_513_);
    return v_res_516_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(
    mut v_x_519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_519_) == 4 {
        let mut v_elems_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_521_: usize = 0;
        let mut v___x_522_: usize = 0;
        let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_520_ = crate::leanh::lean_ctor_get(v_x_519_, 0);
        crate::leanh::lean_inc_ref(v_elems_520_);
        crate::leanh::lean_dec_ref_known(v_x_519_, 1);
        v_sz_521_ = lean_array_size(v_elems_520_);
        v___x_522_ = 0usize;
        v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(v_sz_521_, v___x_522_, v_elems_520_);
        return v___x_523_;
    } else {
        let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_524_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0;
        v___x_525_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_526_ = l_Lean_Json_pretty(v_x_519_, v___x_525_);
        v___x_527_ = lean_string_append(v___x_524_, v___x_526_);
        crate::leanh::lean_dec_ref(v___x_526_);
        v___x_528_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1;
        v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
        v___x_530_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_530_, 0, v___x_529_);
        return v___x_530_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(
    mut v_j_531_: *mut crate::leanh::LeanObject,
    mut v_k_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ = l_Lean_Json_getObjValD(v_j_531_, v_k_532_);
    v___x_534_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(v___x_533_);
    return v___x_534_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0___boxed(
    mut v_j_535_: *mut crate::leanh::LeanObject,
    mut v_k_536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_537_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(v_j_535_, v_k_536_);
    crate::leanh::lean_dec_ref(v_k_536_);
    return v_res_537_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_543_: u8 = 0;
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = 1;
    v___x_544_ = l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1;
    v___x_545_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_544_, v___x_543_);
    return v___x_545_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_546_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5;
    v___x_547_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2,
    );
    v___x_548_ = lean_string_append(v___x_547_, v___x_546_);
    return v___x_548_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = 1;
    v___x_552_ = l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4;
    v___x_553_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_552_, v___x_551_);
    return v___x_553_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5,
    );
    v___x_555_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3,
    );
    v___x_556_ = lean_string_append(v___x_555_, v___x_554_);
    return v___x_556_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_557_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10;
    v___x_558_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6,
    );
    v___x_559_ = lean_string_append(v___x_558_, v___x_557_);
    return v___x_559_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRegistrationParams_fromJson(
    mut v_json_560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_566_: u8 = 0;
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_572_: u8 = 0;
    let mut v_a_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_576_: u8 = 0;
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_580_: u8 = 0;
    let mut v_a_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_561_ = l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0;
                v___x_562_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(v_json_560_, v___x_561_);
                if crate::leanh::lean_obj_tag(v___x_562_) == 0 {
                    v_a_563_ = crate::leanh::lean_ctor_get(v___x_562_, 0);
                    v_isSharedCheck_572_ = (!crate::leanh::lean_is_exclusive(v___x_562_)) as u8;
                    if v_isSharedCheck_572_ == 0 {
                        v___x_565_ = v___x_562_;
                        v_isShared_566_ = v_isSharedCheck_572_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_563_);
                        crate::leanh::lean_dec(v___x_562_);
                        v___x_565_ = crate::leanh::lean_box(0);
                        v_isShared_566_ = v_isSharedCheck_572_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_562_) == 0 {
                        v_a_573_ = crate::leanh::lean_ctor_get(v___x_562_, 0);
                        v_isSharedCheck_580_ = (!crate::leanh::lean_is_exclusive(v___x_562_)) as u8;
                        if v_isSharedCheck_580_ == 0 {
                            v___x_575_ = v___x_562_;
                            v_isShared_576_ = v_isSharedCheck_580_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_573_);
                            crate::leanh::lean_dec(v___x_562_);
                            v___x_575_ = crate::leanh::lean_box(0);
                            v_isShared_576_ = v_isSharedCheck_580_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_581_ = crate::leanh::lean_ctor_get(v___x_562_, 0);
                        v_isSharedCheck_588_ = (!crate::leanh::lean_is_exclusive(v___x_562_)) as u8;
                        if v_isSharedCheck_588_ == 0 {
                            v___x_583_ = v___x_562_;
                            v_isShared_584_ = v_isSharedCheck_588_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_581_);
                            crate::leanh::lean_dec(v___x_562_);
                            v___x_583_ = crate::leanh::lean_box(0);
                            v_isShared_584_ = v_isSharedCheck_588_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_567_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7,
                );
                v___x_568_ = lean_string_append(v___x_567_, v_a_563_);
                crate::leanh::lean_dec(v_a_563_);
                if v_isShared_566_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_565_, 0, v___x_568_);
                    v___x_570_ = v___x_565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
                    v___x_570_ = v_reuseFailAlloc_571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_570_;
            }
            3 => {
                if v_isShared_576_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_575_, 0);
                    v___x_578_ = v___x_575_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
                    v___x_578_ = v_reuseFailAlloc_579_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_578_;
            }
            5 => {
                if v_isShared_584_ == 0 {
                    v___x_586_ = v___x_583_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_587_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
                    v___x_586_ = v_reuseFailAlloc_587_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_586_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Client(
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
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Client(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_Client(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Data_Lsp_Client(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Client(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Client(builtin);
}

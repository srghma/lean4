// Lean compiler output
// Module: Lean.Data.Lsp.Client
// Imports: Lean.Data.Lsp.Basic
use crate::ffi::{
    lean_array_size, lean_array_to_list, lean_array_uget, lean_array_uget_borrowed,
    lean_array_uset, lean_string_append, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::Basic::{
    initialize_Lean_Data_Lsp_Basic, runtime_initialize_Lean_Data_Lsp_Basic,
};
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value:
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
    m_data: [105, 100, 0],
};
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value:
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
    m_data: [109, 101, 116, 104, 111, 100, 0],
};
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__2_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__3_value:
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
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRegistration_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRegistration___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonRegistration: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value:
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value:
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value:
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
    m_data: [82, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value)
            as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value)
            as *mut leanh::LeanObject,
        9349648586579053191 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5_value:
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value)
            as *mut leanh::LeanObject,
        6041859491766292191 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10_value:
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value)
            as *mut leanh::LeanObject,
        10404875796858280754 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instFromJsonRegistration_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonRegistration___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRegistration: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonRegistrationParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonRegistrationParams___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonRegistrationParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value)
            as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
        17292097268730655621 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value)
            as *mut leanh::LeanObject,
        3463206859181389405 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonRegistrationParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonRegistrationParams___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRegistrationParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(
    mut v_x_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_296_) == 0 {
        let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_297_ = leanh::lean_box(0);
        return v___x_297_;
    } else {
        let mut v_val_298_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_298_ = leanh::lean_ctor_get(v_x_296_, 0);
        leanh::lean_inc(v_val_298_);
        return v_val_298_;
    }
}
pub unsafe fn l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0___boxed(
    mut v_x_299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(v_x_299_);
    leanh::lean_dec(v_x_299_);
    return v_res_300_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(
    mut v_a_301_: *mut leanh::LeanObject,
    mut v_a_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_301_) == 0 {
                    v___x_303_ = lean_array_to_list(v_a_302_);
                    return v___x_303_;
                } else {
                    v_head_304_ = leanh::lean_ctor_get(v_a_301_, 0);
                    leanh::lean_inc(v_head_304_);
                    v_tail_305_ = leanh::lean_ctor_get(v_a_301_, 1);
                    leanh::lean_inc(v_tail_305_);
                    leanh::lean_dec_ref_known(v_a_301_, 2);
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
    mut v_x_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_method_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_registerOptions_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_id_314_ = leanh::lean_ctor_get(v_x_313_, 0);
    v_method_315_ = leanh::lean_ctor_get(v_x_313_, 1);
    v_registerOptions_316_ = leanh::lean_ctor_get(v_x_313_, 2);
    v___x_317_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__0;
    leanh::lean_inc_ref(v_id_314_);
    v___x_318_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_318_, 0, v_id_314_);
    v___x_319_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_319_, 0, v___x_317_);
    leanh::lean_ctor_set(v___x_319_, 1, v___x_318_);
    v___x_320_ = leanh::lean_box(0);
    v___x_321_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_321_, 0, v___x_319_);
    leanh::lean_ctor_set(v___x_321_, 1, v___x_320_);
    v___x_322_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__1;
    leanh::lean_inc_ref(v_method_315_);
    v___x_323_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_323_, 0, v_method_315_);
    v___x_324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_324_, 0, v___x_322_);
    leanh::lean_ctor_set(v___x_324_, 1, v___x_323_);
    v___x_325_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_325_, 0, v___x_324_);
    leanh::lean_ctor_set(v___x_325_, 1, v___x_320_);
    v___x_326_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__2;
    v___x_327_ = l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(
        v_registerOptions_316_,
    );
    v___x_328_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_328_, 0, v___x_326_);
    leanh::lean_ctor_set(v___x_328_, 1, v___x_327_);
    v___x_329_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_329_, 0, v___x_328_);
    leanh::lean_ctor_set(v___x_329_, 1, v___x_320_);
    v___x_330_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_330_, 0, v___x_329_);
    leanh::lean_ctor_set(v___x_330_, 1, v___x_320_);
    v___x_331_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_331_, 0, v___x_325_);
    leanh::lean_ctor_set(v___x_331_, 1, v___x_330_);
    v___x_332_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_332_, 0, v___x_321_);
    leanh::lean_ctor_set(v___x_332_, 1, v___x_331_);
    v___x_333_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__3;
    v___x_334_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(v___x_332_, v___x_333_);
    v___x_335_ = l_Lean_Json_mkObj(v___x_334_);
    leanh::lean_dec(v___x_334_);
    return v___x_335_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRegistration_toJson___boxed(
    mut v_x_336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Lean_Lsp_instToJsonRegistration_toJson(v_x_336_);
    leanh::lean_dec_ref(v_x_336_);
    return v_res_337_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(
    mut v_j_340_: *mut leanh::LeanObject,
    mut v_k_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Json_getObjValD(v_j_340_, v_k_341_);
    v___x_343_ = l_Lean_Json_getStr_x3f(v___x_342_);
    return v___x_343_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0___boxed(
    mut v_j_344_: *mut leanh::LeanObject,
    mut v_k_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(
            v_j_344_, v_k_345_,
        );
    leanh::lean_dec_ref(v_k_345_);
    return v_res_346_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(
    mut v_x_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_349_) == 0 {
        let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_350_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0;
        return v___x_350_;
    } else {
        let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_351_, 0, v_x_349_);
        v___x_352_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_352_, 0, v___x_351_);
        return v___x_352_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(
    mut v_j_353_: *mut leanh::LeanObject,
    mut v_k_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = l_Lean_Json_getObjValD(v_j_353_, v_k_354_);
    v___x_356_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(v___x_355_);
    return v___x_356_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1___boxed(
    mut v_j_357_: *mut leanh::LeanObject,
    mut v_k_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_359_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(
            v_j_357_, v_k_358_,
        );
    leanh::lean_dec_ref(v_k_358_);
    return v_res_359_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_367_: u8 = 0;
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_367_ = 1;
    v___x_368_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3;
    v___x_369_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_368_, v___x_367_);
    return v___x_369_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5;
    v___x_372_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4,
    );
    v___x_373_ = lean_string_append(v___x_372_, v___x_371_);
    return v___x_373_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_376_: u8 = 0;
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = 1;
    v___x_377_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7;
    v___x_378_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_377_, v___x_376_);
    return v___x_378_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8,
    );
    v___x_380_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6,
    );
    v___x_381_ = lean_string_append(v___x_380_, v___x_379_);
    return v___x_381_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10;
    v___x_384_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9,
    );
    v___x_385_ = lean_string_append(v___x_384_, v___x_383_);
    return v___x_385_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_388_: u8 = 0;
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = 1;
    v___x_389_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12;
    v___x_390_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_389_, v___x_388_);
    return v___x_390_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13,
    );
    v___x_392_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6,
    );
    v___x_393_ = lean_string_append(v___x_392_, v___x_391_);
    return v___x_393_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10;
    v___x_395_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14,
    );
    v___x_396_ = lean_string_append(v___x_395_, v___x_394_);
    return v___x_396_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRegistration_fromJson(
    mut v_json_397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_403_: u8 = 0;
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_409_: u8 = 0;
    let mut v_a_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_413_: u8 = 0;
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_417_: u8 = 0;
    let mut v_a_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_424_: u8 = 0;
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v_a_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_434_: u8 = 0;
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_438_: u8 = 0;
    let mut v_a_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_445_: u8 = 0;
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_398_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__0;
                leanh::lean_inc(v_json_397_);
                v___x_399_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(v_json_397_, v___x_398_);
                if leanh::lean_obj_tag(v___x_399_) == 0 {
                    leanh::lean_dec(v_json_397_);
                    v_a_400_ = leanh::lean_ctor_get(v___x_399_, 0);
                    v_isSharedCheck_409_ = (!leanh::lean_is_exclusive(v___x_399_)) as u8;
                    if v_isSharedCheck_409_ == 0 {
                        v___x_402_ = v___x_399_;
                        v_isShared_403_ = v_isSharedCheck_409_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_400_);
                        leanh::lean_dec(v___x_399_);
                        v___x_402_ = leanh::lean_box(0);
                        v_isShared_403_ = v_isSharedCheck_409_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_399_) == 0 {
                        leanh::lean_dec(v_json_397_);
                        v_a_410_ = leanh::lean_ctor_get(v___x_399_, 0);
                        v_isSharedCheck_417_ = (!leanh::lean_is_exclusive(v___x_399_)) as u8;
                        if v_isSharedCheck_417_ == 0 {
                            v___x_412_ = v___x_399_;
                            v_isShared_413_ = v_isSharedCheck_417_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_410_);
                            leanh::lean_dec(v___x_399_);
                            v___x_412_ = leanh::lean_box(0);
                            v_isShared_413_ = v_isSharedCheck_417_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_418_ = leanh::lean_ctor_get(v___x_399_, 0);
                        leanh::lean_inc(v_a_418_);
                        leanh::lean_dec_ref_known(v___x_399_, 1);
                        v___x_419_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__1;
                        leanh::lean_inc(v_json_397_);
                        v___x_420_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(v_json_397_, v___x_419_);
                        if leanh::lean_obj_tag(v___x_420_) == 0 {
                            leanh::lean_dec(v_a_418_);
                            leanh::lean_dec(v_json_397_);
                            v_a_421_ = leanh::lean_ctor_get(v___x_420_, 0);
                            v_isSharedCheck_430_ =
                                (!leanh::lean_is_exclusive(v___x_420_)) as u8;
                            if v_isSharedCheck_430_ == 0 {
                                v___x_423_ = v___x_420_;
                                v_isShared_424_ = v_isSharedCheck_430_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_421_);
                                leanh::lean_dec(v___x_420_);
                                v___x_423_ = leanh::lean_box(0);
                                v_isShared_424_ = v_isSharedCheck_430_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_420_) == 0 {
                                leanh::lean_dec(v_a_418_);
                                leanh::lean_dec(v_json_397_);
                                v_a_431_ = leanh::lean_ctor_get(v___x_420_, 0);
                                v_isSharedCheck_438_ =
                                    (!leanh::lean_is_exclusive(v___x_420_)) as u8;
                                if v_isSharedCheck_438_ == 0 {
                                    v___x_433_ = v___x_420_;
                                    v_isShared_434_ = v_isSharedCheck_438_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_431_);
                                    leanh::lean_dec(v___x_420_);
                                    v___x_433_ = leanh::lean_box(0);
                                    v_isShared_434_ = v_isSharedCheck_438_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_439_ = leanh::lean_ctor_get(v___x_420_, 0);
                                leanh::lean_inc(v_a_439_);
                                leanh::lean_dec_ref_known(v___x_420_, 1);
                                v___x_440_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__2;
                                v___x_441_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(v_json_397_, v___x_440_);
                                v_a_442_ = leanh::lean_ctor_get(v___x_441_, 0);
                                v_isSharedCheck_450_ =
                                    (!leanh::lean_is_exclusive(v___x_441_)) as u8;
                                if v_isSharedCheck_450_ == 0 {
                                    v___x_444_ = v___x_441_;
                                    v_isShared_445_ = v_isSharedCheck_450_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_442_);
                                    leanh::lean_dec(v___x_441_);
                                    v___x_444_ = leanh::lean_box(0);
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
                v___x_404_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11,
                );
                v___x_405_ = lean_string_append(v___x_404_, v_a_400_);
                leanh::lean_dec(v_a_400_);
                if v_isShared_403_ == 0 {
                    leanh::lean_ctor_set(v___x_402_, 0, v___x_405_);
                    v___x_407_ = v___x_402_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_408_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
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
                    leanh::lean_ctor_set_tag(v___x_412_, 0);
                    v___x_415_ = v___x_412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_416_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
                    v___x_415_ = v_reuseFailAlloc_416_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_415_;
            }
            5 => {
                v___x_425_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15,
                );
                v___x_426_ = lean_string_append(v___x_425_, v_a_421_);
                leanh::lean_dec(v_a_421_);
                if v_isShared_424_ == 0 {
                    leanh::lean_ctor_set(v___x_423_, 0, v___x_426_);
                    v___x_428_ = v___x_423_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
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
                    leanh::lean_ctor_set_tag(v___x_433_, 0);
                    v___x_436_ = v___x_433_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_437_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
                    v___x_436_ = v_reuseFailAlloc_437_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_436_;
            }
            9 => {
                v___x_446_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_446_, 0, v_a_418_);
                leanh::lean_ctor_set(v___x_446_, 1, v_a_439_);
                leanh::lean_ctor_set(v___x_446_, 2, v_a_442_);
                if v_isShared_445_ == 0 {
                    leanh::lean_ctor_set(v___x_444_, 0, v___x_446_);
                    v___x_448_ = v___x_444_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
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
    mut v_bs_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_456_: u8 = 0;
    let mut v_v_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: usize = 0;
    let mut v___x_462_: usize = 0;
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_456_ = lean_usize_dec_lt(v_i_454_, v_sz_453_);
                if v___x_456_ == 0 {
                    return v_bs_455_;
                } else {
                    v_v_457_ = lean_array_uget(v_bs_455_, v_i_454_);
                    v___x_458_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_459_ = lean_array_uset(v_bs_455_, v_i_454_, v___x_458_);
                    v___x_460_ = l_Lean_Lsp_instToJsonRegistration_toJson(v_v_457_);
                    leanh::lean_dec(v_v_457_);
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
    mut v_sz_465_: *mut leanh::LeanObject,
    mut v_i_466_: *mut leanh::LeanObject,
    mut v_bs_467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_468_: usize = 0;
    let mut v_i_boxed_469_: usize = 0;
    let mut v_res_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_468_ = leanh::lean_unbox_usize(v_sz_465_);
    leanh::lean_dec(v_sz_465_);
    v_i_boxed_469_ = leanh::lean_unbox_usize(v_i_466_);
    leanh::lean_dec(v_i_466_);
    v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(v_sz_boxed_468_, v_i_boxed_469_, v_bs_467_);
    return v_res_470_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(
    mut v_a_471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_472_: usize = 0;
    let mut v___x_473_: usize = 0;
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_472_ = lean_array_size(v_a_471_);
    v___x_473_ = 0usize;
    v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(v_sz_472_, v___x_473_, v_a_471_);
    v___x_475_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_475_, 0, v___x_474_);
    return v___x_475_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRegistrationParams_toJson(
    mut v_x_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_478_ = l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0;
    v___x_479_ =
        l_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(v_x_477_);
    v___x_480_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_480_, 0, v___x_478_);
    leanh::lean_ctor_set(v___x_480_, 1, v___x_479_);
    v___x_481_ = leanh::lean_box(0);
    v___x_482_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_482_, 0, v___x_480_);
    leanh::lean_ctor_set(v___x_482_, 1, v___x_481_);
    v___x_483_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_483_, 0, v___x_482_);
    leanh::lean_ctor_set(v___x_483_, 1, v___x_481_);
    v___x_484_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__3;
    v___x_485_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(v___x_483_, v___x_484_);
    v___x_486_ = l_Lean_Json_mkObj(v___x_485_);
    leanh::lean_dec(v___x_485_);
    return v___x_486_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(
    mut v_sz_489_: usize,
    mut v_i_490_: usize,
    mut v_bs_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_492_: u8 = 0;
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_499_: u8 = 0;
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_503_: u8 = 0;
    let mut v_a_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: usize = 0;
    let mut v___x_508_: usize = 0;
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_492_ = lean_usize_dec_lt(v_i_490_, v_sz_489_);
                if v___x_492_ == 0 {
                    v___x_493_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_493_, 0, v_bs_491_);
                    return v___x_493_;
                } else {
                    v_v_494_ = lean_array_uget_borrowed(v_bs_491_, v_i_490_);
                    leanh::lean_inc(v_v_494_);
                    v___x_495_ = l_Lean_Lsp_instFromJsonRegistration_fromJson(v_v_494_);
                    if leanh::lean_obj_tag(v___x_495_) == 0 {
                        leanh::lean_dec_ref(v_bs_491_);
                        v_a_496_ = leanh::lean_ctor_get(v___x_495_, 0);
                        v_isSharedCheck_503_ = (!leanh::lean_is_exclusive(v___x_495_)) as u8;
                        if v_isSharedCheck_503_ == 0 {
                            v___x_498_ = v___x_495_;
                            v_isShared_499_ = v_isSharedCheck_503_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_496_);
                            leanh::lean_dec(v___x_495_);
                            v___x_498_ = leanh::lean_box(0);
                            v_isShared_499_ = v_isSharedCheck_503_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_504_ = leanh::lean_ctor_get(v___x_495_, 0);
                        leanh::lean_inc(v_a_504_);
                        leanh::lean_dec_ref_known(v___x_495_, 1);
                        v___x_505_ = leanh::lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_502_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
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
    mut v_sz_511_: *mut leanh::LeanObject,
    mut v_i_512_: *mut leanh::LeanObject,
    mut v_bs_513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_514_: usize = 0;
    let mut v_i_boxed_515_: usize = 0;
    let mut v_res_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_514_ = leanh::lean_unbox_usize(v_sz_511_);
    leanh::lean_dec(v_sz_511_);
    v_i_boxed_515_ = leanh::lean_unbox_usize(v_i_512_);
    leanh::lean_dec(v_i_512_);
    v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_514_, v_i_boxed_515_, v_bs_513_);
    return v_res_516_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(
    mut v_x_519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_519_) == 4 {
        let mut v_elems_520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_521_: usize = 0;
        let mut v___x_522_: usize = 0;
        let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_520_ = leanh::lean_ctor_get(v_x_519_, 0);
        leanh::lean_inc_ref(v_elems_520_);
        leanh::lean_dec_ref_known(v_x_519_, 1);
        v_sz_521_ = lean_array_size(v_elems_520_);
        v___x_522_ = 0usize;
        v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(v_sz_521_, v___x_522_, v_elems_520_);
        return v___x_523_;
    } else {
        let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_524_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0;
        v___x_525_ = leanh::lean_unsigned_to_nat(80);
        v___x_526_ = l_Lean_Json_pretty(v_x_519_, v___x_525_);
        v___x_527_ = lean_string_append(v___x_524_, v___x_526_);
        leanh::lean_dec_ref(v___x_526_);
        v___x_528_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1;
        v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
        v___x_530_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_530_, 0, v___x_529_);
        return v___x_530_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(
    mut v_j_531_: *mut leanh::LeanObject,
    mut v_k_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ = l_Lean_Json_getObjValD(v_j_531_, v_k_532_);
    v___x_534_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(v___x_533_);
    return v___x_534_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0___boxed(
    mut v_j_535_: *mut leanh::LeanObject,
    mut v_k_536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_537_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(v_j_535_, v_k_536_);
    leanh::lean_dec_ref(v_k_536_);
    return v_res_537_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_543_: u8 = 0;
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = 1;
    v___x_544_ = l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1;
    v___x_545_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_544_, v___x_543_);
    return v___x_545_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_546_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5;
    v___x_547_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = 1;
    v___x_552_ = l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4;
    v___x_553_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_552_, v___x_551_);
    return v___x_553_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5,
    );
    v___x_555_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_557_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10;
    v___x_558_ = leanh::lean_obj_once(
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
    mut v_json_560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_566_: u8 = 0;
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_572_: u8 = 0;
    let mut v_a_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_576_: u8 = 0;
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_580_: u8 = 0;
    let mut v_a_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_561_ = l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0;
                v___x_562_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(v_json_560_, v___x_561_);
                if leanh::lean_obj_tag(v___x_562_) == 0 {
                    v_a_563_ = leanh::lean_ctor_get(v___x_562_, 0);
                    v_isSharedCheck_572_ = (!leanh::lean_is_exclusive(v___x_562_)) as u8;
                    if v_isSharedCheck_572_ == 0 {
                        v___x_565_ = v___x_562_;
                        v_isShared_566_ = v_isSharedCheck_572_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_563_);
                        leanh::lean_dec(v___x_562_);
                        v___x_565_ = leanh::lean_box(0);
                        v_isShared_566_ = v_isSharedCheck_572_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_562_) == 0 {
                        v_a_573_ = leanh::lean_ctor_get(v___x_562_, 0);
                        v_isSharedCheck_580_ = (!leanh::lean_is_exclusive(v___x_562_)) as u8;
                        if v_isSharedCheck_580_ == 0 {
                            v___x_575_ = v___x_562_;
                            v_isShared_576_ = v_isSharedCheck_580_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_573_);
                            leanh::lean_dec(v___x_562_);
                            v___x_575_ = leanh::lean_box(0);
                            v_isShared_576_ = v_isSharedCheck_580_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_581_ = leanh::lean_ctor_get(v___x_562_, 0);
                        v_isSharedCheck_588_ = (!leanh::lean_is_exclusive(v___x_562_)) as u8;
                        if v_isSharedCheck_588_ == 0 {
                            v___x_583_ = v___x_562_;
                            v_isShared_584_ = v_isSharedCheck_588_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_581_);
                            leanh::lean_dec(v___x_562_);
                            v___x_583_ = leanh::lean_box(0);
                            v_isShared_584_ = v_isSharedCheck_588_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_567_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7,
                );
                v___x_568_ = lean_string_append(v___x_567_, v_a_563_);
                leanh::lean_dec(v_a_563_);
                if v_isShared_566_ == 0 {
                    leanh::lean_ctor_set(v___x_565_, 0, v___x_568_);
                    v___x_570_ = v___x_565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
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
                    leanh::lean_ctor_set_tag(v___x_575_, 0);
                    v___x_578_ = v___x_575_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_579_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
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
                    v_reuseFailAlloc_587_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
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
pub unsafe fn meta_initialize_Lean_Data_Lsp_Client(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_Client(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Lean_Data_Lsp_Client(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Client(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Client(builtin);
}
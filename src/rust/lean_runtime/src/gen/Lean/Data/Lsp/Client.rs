// Lean compiler output
// Module: Lean.Data.Lsp.Client
// Imports: Lean.Data.Lsp.Basic
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
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
    lean_array_to_list, lean_mk_empty_array_with_capacity,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__2_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration_toJson___closed__3_value: LeanArrayObject<0> =
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
static mut l_Lean_Lsp_instToJsonRegistration_toJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRegistration___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRegistration_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRegistration___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonRegistration: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value)
                as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value)
                as *mut LeanObject,
            9349648586579053191 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value)
                as *mut LeanObject,
            6041859491766292191 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value)
                as *mut LeanObject,
            10404875796858280754 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistration___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonRegistration_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonRegistration___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRegistration: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRegistrationParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRegistrationParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonRegistrationParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value)
        as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value: LeanStringObject<
    19,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value)
            as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value
            ) as *mut LeanObject,
            17292097268730655621 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value)
                as *mut LeanObject,
            3463206859181389405 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonRegistrationParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonRegistrationParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRegistrationParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(
    mut v_x_296_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_296_) == 0 {
        let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
        v___x_297_ = lean_box(0);
        return v___x_297_;
    } else {
        let mut v_val_298_: *mut LeanObject = core::ptr::null_mut();
        v_val_298_ = lean_ctor_get(v_x_296_, 0);
        lean_inc(v_val_298_);
        return v_val_298_;
    }
}
pub unsafe fn l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0___boxed(
    mut v_x_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_300_: *mut LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(v_x_299_);
    lean_dec(v_x_299_);
    return v_res_300_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(
    mut v_a_301_: *mut LeanObject,
    mut v_a_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_301_) == 0 {
                    v___x_303_ = lean_array_to_list(v_a_302_);
                    return v___x_303_;
                } else {
                    v_head_304_ = lean_ctor_get(v_a_301_, 0);
                    lean_inc(v_head_304_);
                    v_tail_305_ = lean_ctor_get(v_a_301_, 1);
                    lean_inc(v_tail_305_);
                    lean_dec_ref_known(v_a_301_, 2);
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
    mut v_x_313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_method_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_registerOptions_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    v_id_314_ = lean_ctor_get(v_x_313_, 0);
    v_method_315_ = lean_ctor_get(v_x_313_, 1);
    v_registerOptions_316_ = lean_ctor_get(v_x_313_, 2);
    v___x_317_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__0;
    lean_inc_ref(v_id_314_);
    v___x_318_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_318_, 0, v_id_314_);
    v___x_319_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_319_, 0, v___x_317_);
    lean_ctor_set(v___x_319_, 1, v___x_318_);
    v___x_320_ = lean_box(0);
    v___x_321_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_321_, 0, v___x_319_);
    lean_ctor_set(v___x_321_, 1, v___x_320_);
    v___x_322_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__1;
    lean_inc_ref(v_method_315_);
    v___x_323_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_323_, 0, v_method_315_);
    v___x_324_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_324_, 0, v___x_322_);
    lean_ctor_set(v___x_324_, 1, v___x_323_);
    v___x_325_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_325_, 0, v___x_324_);
    lean_ctor_set(v___x_325_, 1, v___x_320_);
    v___x_326_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__2;
    v___x_327_ = l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(
        v_registerOptions_316_,
    );
    v___x_328_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_328_, 0, v___x_326_);
    lean_ctor_set(v___x_328_, 1, v___x_327_);
    v___x_329_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_329_, 0, v___x_328_);
    lean_ctor_set(v___x_329_, 1, v___x_320_);
    v___x_330_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_330_, 0, v___x_329_);
    lean_ctor_set(v___x_330_, 1, v___x_320_);
    v___x_331_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_331_, 0, v___x_325_);
    lean_ctor_set(v___x_331_, 1, v___x_330_);
    v___x_332_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_332_, 0, v___x_321_);
    lean_ctor_set(v___x_332_, 1, v___x_331_);
    v___x_333_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__3;
    v___x_334_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(v___x_332_, v___x_333_);
    v___x_335_ = l_Lean_Json_mkObj(v___x_334_);
    lean_dec(v___x_334_);
    return v___x_335_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRegistration_toJson___boxed(
    mut v_x_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_337_: *mut LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Lean_Lsp_instToJsonRegistration_toJson(v_x_336_);
    lean_dec_ref(v_x_336_);
    return v_res_337_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(
    mut v_j_340_: *mut LeanObject,
    mut v_k_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Json_getObjValD(v_j_340_, v_k_341_);
    v___x_343_ = l_Lean_Json_getStr_x3f(v___x_342_);
    return v___x_343_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0___boxed(
    mut v_j_344_: *mut LeanObject,
    mut v_k_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_346_: *mut LeanObject = core::ptr::null_mut();
    v_res_346_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(
            v_j_344_, v_k_345_,
        );
    lean_dec_ref(v_k_345_);
    return v_res_346_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(
    mut v_x_349_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_349_) == 0 {
        let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
        v___x_350_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0;
        return v___x_350_;
    } else {
        let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
        v___x_351_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_351_, 0, v_x_349_);
        v___x_352_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_352_, 0, v___x_351_);
        return v___x_352_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(
    mut v_j_353_: *mut LeanObject,
    mut v_k_354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    v___x_355_ = l_Lean_Json_getObjValD(v_j_353_, v_k_354_);
    v___x_356_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(v___x_355_);
    return v___x_356_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1___boxed(
    mut v_j_357_: *mut LeanObject,
    mut v_k_358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_359_: *mut LeanObject = core::ptr::null_mut();
    v_res_359_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(
            v_j_357_, v_k_358_,
        );
    lean_dec_ref(v_k_358_);
    return v_res_359_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_367_: u8 = 0;
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    v___x_367_ = 1;
    v___x_368_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3;
    v___x_369_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_368_, v___x_367_);
    return v___x_369_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    v___x_371_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5;
    v___x_372_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4,
    );
    v___x_373_ = lean_string_append(v___x_372_, v___x_371_);
    return v___x_373_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_376_: u8 = 0;
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    v___x_376_ = 1;
    v___x_377_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7;
    v___x_378_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_377_, v___x_376_);
    return v___x_378_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    v___x_379_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8,
    );
    v___x_380_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6,
    );
    v___x_381_ = lean_string_append(v___x_380_, v___x_379_);
    return v___x_381_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11() -> *mut LeanObject {
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    v___x_383_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10;
    v___x_384_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9,
    );
    v___x_385_ = lean_string_append(v___x_384_, v___x_383_);
    return v___x_385_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13() -> *mut LeanObject {
    let mut v___x_388_: u8 = 0;
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    v___x_388_ = 1;
    v___x_389_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12;
    v___x_390_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_389_, v___x_388_);
    return v___x_390_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14() -> *mut LeanObject {
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    v___x_391_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13,
    );
    v___x_392_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6,
    );
    v___x_393_ = lean_string_append(v___x_392_, v___x_391_);
    return v___x_393_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15() -> *mut LeanObject {
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    v___x_394_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10;
    v___x_395_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14,
    );
    v___x_396_ = lean_string_append(v___x_395_, v___x_394_);
    return v___x_396_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRegistration_fromJson(
    mut v_json_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_403_: u8 = 0;
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_409_: u8 = 0;
    let mut v_a_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_413_: u8 = 0;
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_417_: u8 = 0;
    let mut v_a_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_424_: u8 = 0;
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v_a_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_434_: u8 = 0;
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_438_: u8 = 0;
    let mut v_a_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_445_: u8 = 0;
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_398_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__0;
                lean_inc(v_json_397_);
                v___x_399_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(v_json_397_, v___x_398_);
                if lean_obj_tag(v___x_399_) == 0 {
                    lean_dec(v_json_397_);
                    v_a_400_ = lean_ctor_get(v___x_399_, 0);
                    v_isSharedCheck_409_ = (!lean_is_exclusive(v___x_399_)) as u8;
                    if v_isSharedCheck_409_ == 0 {
                        v___x_402_ = v___x_399_;
                        v_isShared_403_ = v_isSharedCheck_409_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_400_);
                        lean_dec(v___x_399_);
                        v___x_402_ = lean_box(0);
                        v_isShared_403_ = v_isSharedCheck_409_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_399_) == 0 {
                        lean_dec(v_json_397_);
                        v_a_410_ = lean_ctor_get(v___x_399_, 0);
                        v_isSharedCheck_417_ = (!lean_is_exclusive(v___x_399_)) as u8;
                        if v_isSharedCheck_417_ == 0 {
                            v___x_412_ = v___x_399_;
                            v_isShared_413_ = v_isSharedCheck_417_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_410_);
                            lean_dec(v___x_399_);
                            v___x_412_ = lean_box(0);
                            v_isShared_413_ = v_isSharedCheck_417_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_418_ = lean_ctor_get(v___x_399_, 0);
                        lean_inc(v_a_418_);
                        lean_dec_ref_known(v___x_399_, 1);
                        v___x_419_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__1;
                        lean_inc(v_json_397_);
                        v___x_420_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(v_json_397_, v___x_419_);
                        if lean_obj_tag(v___x_420_) == 0 {
                            lean_dec(v_a_418_);
                            lean_dec(v_json_397_);
                            v_a_421_ = lean_ctor_get(v___x_420_, 0);
                            v_isSharedCheck_430_ = (!lean_is_exclusive(v___x_420_)) as u8;
                            if v_isSharedCheck_430_ == 0 {
                                v___x_423_ = v___x_420_;
                                v_isShared_424_ = v_isSharedCheck_430_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_421_);
                                lean_dec(v___x_420_);
                                v___x_423_ = lean_box(0);
                                v_isShared_424_ = v_isSharedCheck_430_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_420_) == 0 {
                                lean_dec(v_a_418_);
                                lean_dec(v_json_397_);
                                v_a_431_ = lean_ctor_get(v___x_420_, 0);
                                v_isSharedCheck_438_ = (!lean_is_exclusive(v___x_420_)) as u8;
                                if v_isSharedCheck_438_ == 0 {
                                    v___x_433_ = v___x_420_;
                                    v_isShared_434_ = v_isSharedCheck_438_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_431_);
                                    lean_dec(v___x_420_);
                                    v___x_433_ = lean_box(0);
                                    v_isShared_434_ = v_isSharedCheck_438_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_439_ = lean_ctor_get(v___x_420_, 0);
                                lean_inc(v_a_439_);
                                lean_dec_ref_known(v___x_420_, 1);
                                v___x_440_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__2;
                                v___x_441_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(v_json_397_, v___x_440_);
                                v_a_442_ = lean_ctor_get(v___x_441_, 0);
                                v_isSharedCheck_450_ = (!lean_is_exclusive(v___x_441_)) as u8;
                                if v_isSharedCheck_450_ == 0 {
                                    v___x_444_ = v___x_441_;
                                    v_isShared_445_ = v_isSharedCheck_450_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_442_);
                                    lean_dec(v___x_441_);
                                    v___x_444_ = lean_box(0);
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
                v___x_404_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11,
                );
                v___x_405_ = lean_string_append(v___x_404_, v_a_400_);
                lean_dec(v_a_400_);
                if v_isShared_403_ == 0 {
                    lean_ctor_set(v___x_402_, 0, v___x_405_);
                    v___x_407_ = v___x_402_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
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
                    lean_ctor_set_tag(v___x_412_, 0);
                    v___x_415_ = v___x_412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
                    v___x_415_ = v_reuseFailAlloc_416_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_415_;
            }
            5 => {
                v___x_425_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15,
                );
                v___x_426_ = lean_string_append(v___x_425_, v_a_421_);
                lean_dec(v_a_421_);
                if v_isShared_424_ == 0 {
                    lean_ctor_set(v___x_423_, 0, v___x_426_);
                    v___x_428_ = v___x_423_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
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
                    lean_ctor_set_tag(v___x_433_, 0);
                    v___x_436_ = v___x_433_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
                    v___x_436_ = v_reuseFailAlloc_437_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_436_;
            }
            9 => {
                v___x_446_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_446_, 0, v_a_418_);
                lean_ctor_set(v___x_446_, 1, v_a_439_);
                lean_ctor_set(v___x_446_, 2, v_a_442_);
                if v_isShared_445_ == 0 {
                    lean_ctor_set(v___x_444_, 0, v___x_446_);
                    v___x_448_ = v___x_444_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
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
    mut v_bs_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_456_: u8 = 0;
    let mut v_v_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: usize = 0;
    let mut v___x_462_: usize = 0;
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_456_ = lean_usize_dec_lt(v_i_454_, v_sz_453_);
                if v___x_456_ == 0 {
                    return v_bs_455_;
                } else {
                    v_v_457_ = lean_array_uget(v_bs_455_, v_i_454_);
                    v___x_458_ = lean_unsigned_to_nat(0);
                    v_bs_x27_459_ = lean_array_uset(v_bs_455_, v_i_454_, v___x_458_);
                    v___x_460_ = l_Lean_Lsp_instToJsonRegistration_toJson(v_v_457_);
                    lean_dec(v_v_457_);
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
    mut v_sz_465_: *mut LeanObject,
    mut v_i_466_: *mut LeanObject,
    mut v_bs_467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_468_: usize = 0;
    let mut v_i_boxed_469_: usize = 0;
    let mut v_res_470_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_468_ = lean_unbox_usize(v_sz_465_);
    lean_dec(v_sz_465_);
    v_i_boxed_469_ = lean_unbox_usize(v_i_466_);
    lean_dec(v_i_466_);
    v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(v_sz_boxed_468_, v_i_boxed_469_, v_bs_467_);
    return v_res_470_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(
    mut v_a_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_472_: usize = 0;
    let mut v___x_473_: usize = 0;
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v_sz_472_ = lean_array_size(v_a_471_);
    v___x_473_ = 0usize;
    v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(v_sz_472_, v___x_473_, v_a_471_);
    v___x_475_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_475_, 0, v___x_474_);
    return v___x_475_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRegistrationParams_toJson(
    mut v_x_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v___x_478_ = l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0;
    v___x_479_ =
        l_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(v_x_477_);
    v___x_480_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_480_, 0, v___x_478_);
    lean_ctor_set(v___x_480_, 1, v___x_479_);
    v___x_481_ = lean_box(0);
    v___x_482_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_482_, 0, v___x_480_);
    lean_ctor_set(v___x_482_, 1, v___x_481_);
    v___x_483_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_483_, 0, v___x_482_);
    lean_ctor_set(v___x_483_, 1, v___x_481_);
    v___x_484_ = l_Lean_Lsp_instToJsonRegistration_toJson___closed__3;
    v___x_485_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(v___x_483_, v___x_484_);
    v___x_486_ = l_Lean_Json_mkObj(v___x_485_);
    lean_dec(v___x_485_);
    return v___x_486_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(
    mut v_sz_489_: usize,
    mut v_i_490_: usize,
    mut v_bs_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_492_: u8 = 0;
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_499_: u8 = 0;
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_503_: u8 = 0;
    let mut v_a_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: usize = 0;
    let mut v___x_508_: usize = 0;
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_492_ = lean_usize_dec_lt(v_i_490_, v_sz_489_);
                if v___x_492_ == 0 {
                    v___x_493_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_493_, 0, v_bs_491_);
                    return v___x_493_;
                } else {
                    v_v_494_ = lean_array_uget_borrowed(v_bs_491_, v_i_490_);
                    lean_inc(v_v_494_);
                    v___x_495_ = l_Lean_Lsp_instFromJsonRegistration_fromJson(v_v_494_);
                    if lean_obj_tag(v___x_495_) == 0 {
                        lean_dec_ref(v_bs_491_);
                        v_a_496_ = lean_ctor_get(v___x_495_, 0);
                        v_isSharedCheck_503_ = (!lean_is_exclusive(v___x_495_)) as u8;
                        if v_isSharedCheck_503_ == 0 {
                            v___x_498_ = v___x_495_;
                            v_isShared_499_ = v_isSharedCheck_503_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_496_);
                            lean_dec(v___x_495_);
                            v___x_498_ = lean_box(0);
                            v_isShared_499_ = v_isSharedCheck_503_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_504_ = lean_ctor_get(v___x_495_, 0);
                        lean_inc(v_a_504_);
                        lean_dec_ref_known(v___x_495_, 1);
                        v___x_505_ = lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
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
    mut v_sz_511_: *mut LeanObject,
    mut v_i_512_: *mut LeanObject,
    mut v_bs_513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_514_: usize = 0;
    let mut v_i_boxed_515_: usize = 0;
    let mut v_res_516_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_514_ = lean_unbox_usize(v_sz_511_);
    lean_dec(v_sz_511_);
    v_i_boxed_515_ = lean_unbox_usize(v_i_512_);
    lean_dec(v_i_512_);
    v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_514_, v_i_boxed_515_, v_bs_513_);
    return v_res_516_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(
    mut v_x_519_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_519_) == 4 {
        let mut v_elems_520_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_521_: usize = 0;
        let mut v___x_522_: usize = 0;
        let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
        v_elems_520_ = lean_ctor_get(v_x_519_, 0);
        lean_inc_ref(v_elems_520_);
        lean_dec_ref_known(v_x_519_, 1);
        v_sz_521_ = lean_array_size(v_elems_520_);
        v___x_522_ = 0usize;
        v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(v_sz_521_, v___x_522_, v_elems_520_);
        return v___x_523_;
    } else {
        let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
        v___x_524_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0;
        v___x_525_ = lean_unsigned_to_nat(80);
        v___x_526_ = l_Lean_Json_pretty(v_x_519_, v___x_525_);
        v___x_527_ = lean_string_append(v___x_524_, v___x_526_);
        lean_dec_ref(v___x_526_);
        v___x_528_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1;
        v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
        v___x_530_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_530_, 0, v___x_529_);
        return v___x_530_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(
    mut v_j_531_: *mut LeanObject,
    mut v_k_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    v___x_533_ = l_Lean_Json_getObjValD(v_j_531_, v_k_532_);
    v___x_534_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(v___x_533_);
    return v___x_534_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0___boxed(
    mut v_j_535_: *mut LeanObject,
    mut v_k_536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_537_: *mut LeanObject = core::ptr::null_mut();
    v_res_537_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(v_j_535_, v_k_536_);
    lean_dec_ref(v_k_536_);
    return v_res_537_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_543_: u8 = 0;
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    v___x_543_ = 1;
    v___x_544_ = l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1;
    v___x_545_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_544_, v___x_543_);
    return v___x_545_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    v___x_546_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5;
    v___x_547_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    v___x_551_ = 1;
    v___x_552_ = l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4;
    v___x_553_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_552_, v___x_551_);
    return v___x_553_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    v___x_554_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5,
    );
    v___x_555_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    v___x_557_ = l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10;
    v___x_558_ = lean_obj_once(
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
    mut v_json_560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_566_: u8 = 0;
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_572_: u8 = 0;
    let mut v_a_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_576_: u8 = 0;
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_580_: u8 = 0;
    let mut v_a_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_561_ = l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0;
                v___x_562_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(v_json_560_, v___x_561_);
                if lean_obj_tag(v___x_562_) == 0 {
                    v_a_563_ = lean_ctor_get(v___x_562_, 0);
                    v_isSharedCheck_572_ = (!lean_is_exclusive(v___x_562_)) as u8;
                    if v_isSharedCheck_572_ == 0 {
                        v___x_565_ = v___x_562_;
                        v_isShared_566_ = v_isSharedCheck_572_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_563_);
                        lean_dec(v___x_562_);
                        v___x_565_ = lean_box(0);
                        v_isShared_566_ = v_isSharedCheck_572_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_562_) == 0 {
                        v_a_573_ = lean_ctor_get(v___x_562_, 0);
                        v_isSharedCheck_580_ = (!lean_is_exclusive(v___x_562_)) as u8;
                        if v_isSharedCheck_580_ == 0 {
                            v___x_575_ = v___x_562_;
                            v_isShared_576_ = v_isSharedCheck_580_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_573_);
                            lean_dec(v___x_562_);
                            v___x_575_ = lean_box(0);
                            v_isShared_576_ = v_isSharedCheck_580_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_581_ = lean_ctor_get(v___x_562_, 0);
                        v_isSharedCheck_588_ = (!lean_is_exclusive(v___x_562_)) as u8;
                        if v_isSharedCheck_588_ == 0 {
                            v___x_583_ = v___x_562_;
                            v_isShared_584_ = v_isSharedCheck_588_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_581_);
                            lean_dec(v___x_562_);
                            v___x_583_ = lean_box(0);
                            v_isShared_584_ = v_isSharedCheck_588_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_567_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7,
                );
                v___x_568_ = lean_string_append(v___x_567_, v_a_563_);
                lean_dec(v_a_563_);
                if v_isShared_566_ == 0 {
                    lean_ctor_set(v___x_565_, 0, v___x_568_);
                    v___x_570_ = v___x_565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
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
                    lean_ctor_set_tag(v___x_575_, 0);
                    v___x_578_ = v___x_575_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
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
                    v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
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
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Client(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Client(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_Client(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Client(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Client(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Client(builtin);
}

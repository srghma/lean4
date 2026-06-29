// Lean compiler output
// Module: Lake.Build.ModuleArtifacts
// Imports: Lake.Config.Artifact Lake.Util.JsonObject
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_string_append, lean_string_utf8_byte_size,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Lake::Config::Artifact::{
    initialize_Lake_Config_Artifact, l_Lake_ArtifactDescr_fromJson_x3f,
    runtime_initialize_Lake_Config_Artifact,
};
use crate::r#gen::Lake::Util::JsonObject::{
    initialize_Lake_Util_JsonObject, l_Lake_JsonObject_getJson_x3f, l_Lake_JsonObject_insertJson,
    runtime_initialize_Lake_Util_JsonObject,
};
use crate::r#gen::Lake::Util::String::l_Lake_lowerHexUInt64;
use crate::r#gen::Lean::Data::Json::Basic::{l_Lean_Json_getBool_x3f, l_Lean_Json_getObj_x3f};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [108, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [98, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [99, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__3_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [109, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__4_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [111, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__5_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [105, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__6_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [114, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToJsonModuleOutputDescrs___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_ModuleOutputDescrs_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToJsonModuleOutputDescrs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonModuleOutputDescrs___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToJsonModuleOutputDescrs: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonModuleOutputDescrs___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58,
        32, 111, 0,
    ],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2_value:
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
    m_data: [111, 58, 32, 0],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 108, 101, 97, 115, 116, 32, 111, 110,
        101, 32, 39, 111, 39, 32, 40, 46, 111, 108, 101, 97, 110, 41, 32, 104, 97, 115, 104, 0,
    ],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value:
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
    m_data: [108, 58, 32, 0],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58,
        32, 99, 0,
    ],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value:
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
    m_data: [99, 58, 32, 0],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value:
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
    m_data: [98, 58, 32, 0],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58,
        32, 105, 0,
    ],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value:
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
    m_data: [105, 58, 32, 0],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13_value:
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
    m_data: [114, 58, 32, 0],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14_value:
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
    m_data: [109, 58, 32, 0],
};
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonModuleOutputDescrs___closed__0_value:
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
    m_fun: l_Lake_ModuleOutputDescrs_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instFromJsonModuleOutputDescrs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonModuleOutputDescrs___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instFromJsonModuleOutputDescrs: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonModuleOutputDescrs___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_ModuleOutputDescrs_oleanParts(
    mut v_self_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_olean_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanServer_x3f_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanPrivate_x3f_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descrs_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descrs_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descrs_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descrs_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_olean_622_ = crate::leanh::lean_ctor_get(v_self_621_, 0);
                crate::leanh::lean_inc_ref(v_olean_622_);
                v_oleanServer_x3f_623_ = crate::leanh::lean_ctor_get(v_self_621_, 1);
                crate::leanh::lean_inc(v_oleanServer_x3f_623_);
                v_oleanPrivate_x3f_624_ = crate::leanh::lean_ctor_get(v_self_621_, 2);
                crate::leanh::lean_inc(v_oleanPrivate_x3f_624_);
                crate::leanh::lean_dec_ref(v_self_621_);
                v___x_629_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_630_ = lean_mk_empty_array_with_capacity(v___x_629_);
                v_descrs_631_ = lean_array_push(v___x_630_, v_olean_622_);
                if crate::leanh::lean_obj_tag(v_oleanServer_x3f_623_) == 1 {
                    v_val_632_ = crate::leanh::lean_ctor_get(v_oleanServer_x3f_623_, 0);
                    crate::leanh::lean_inc(v_val_632_);
                    crate::leanh::lean_dec_ref_known(v_oleanServer_x3f_623_, 1);
                    v_descrs_633_ = lean_array_push(v_descrs_631_, v_val_632_);
                    v_descrs_626_ = v_descrs_633_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_oleanServer_x3f_623_);
                    v_descrs_626_ = v_descrs_631_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_oleanPrivate_x3f_624_) == 1 {
                    v_val_627_ = crate::leanh::lean_ctor_get(v_oleanPrivate_x3f_624_, 0);
                    crate::leanh::lean_inc(v_val_627_);
                    crate::leanh::lean_dec_ref_known(v_oleanPrivate_x3f_624_, 1);
                    v_descrs_628_ = lean_array_push(v_descrs_626_, v_val_627_);
                    return v_descrs_628_;
                } else {
                    crate::leanh::lean_dec(v_oleanPrivate_x3f_624_);
                    return v_descrs_626_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(
    mut v_sz_635_: usize,
    mut v_i_636_: usize,
    mut v_bs_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_638_: u8 = 0;
    let mut v_v_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_640_: u64 = 0;
    let mut v_ext_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: usize = 0;
    let mut v___x_648_: usize = 0;
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_638_ = lean_usize_dec_lt(v_i_636_, v_sz_635_);
                if v___x_638_ == 0 {
                    return v_bs_637_;
                } else {
                    v_v_639_ = lean_array_uget_borrowed(v_bs_637_, v_i_636_);
                    v_hash_640_ = crate::leanh::lean_ctor_get_uint64(
                        v_v_639_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_ext_641_ = crate::leanh::lean_ctor_get(v_v_639_, 0);
                    crate::leanh::lean_inc_ref(v_ext_641_);
                    v___x_642_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_643_ = lean_array_uset(v_bs_637_, v_i_636_, v___x_642_);
                    v___x_651_ = lean_string_utf8_byte_size(v_ext_641_);
                    v___x_652_ = lean_nat_dec_eq(v___x_651_, v___x_642_);
                    if v___x_652_ == 0 {
                        v___x_653_ = l_Lake_lowerHexUInt64(v_hash_640_);
                        v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                        v___x_655_ = lean_string_append(v___x_653_, v___x_654_);
                        v___x_656_ = lean_string_append(v___x_655_, v_ext_641_);
                        crate::leanh::lean_dec_ref(v_ext_641_);
                        v___y_645_ = v___x_656_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_ext_641_);
                        v___x_657_ = l_Lake_lowerHexUInt64(v_hash_640_);
                        v___y_645_ = v___x_657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_646_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_646_, 0, v___y_645_);
                v___x_647_ = 1usize;
                v___x_648_ = lean_usize_add(v_i_636_, v___x_647_);
                v___x_649_ = lean_array_uset(v_bs_x27_643_, v_i_636_, v___x_646_);
                v_i_636_ = v___x_648_;
                v_bs_637_ = v___x_649_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___boxed(
    mut v_sz_658_: *mut crate::leanh::LeanObject,
    mut v_i_659_: *mut crate::leanh::LeanObject,
    mut v_bs_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_661_: usize = 0;
    let mut v_i_boxed_662_: usize = 0;
    let mut v_res_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_661_ = crate::leanh::lean_unbox_usize(v_sz_658_);
    crate::leanh::lean_dec(v_sz_658_);
    v_i_boxed_662_ = crate::leanh::lean_unbox_usize(v_i_659_);
    crate::leanh::lean_dec(v_i_659_);
    v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_boxed_661_, v_i_boxed_662_, v_bs_660_);
    return v_res_663_;
}
pub unsafe fn l_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(
    mut v_a_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_665_: usize = 0;
    let mut v___x_666_: usize = 0;
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_665_ = lean_array_size(v_a_664_);
    v___x_666_ = 0usize;
    v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_665_, v___x_666_, v_a_664_);
    v___x_668_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_668_, 0, v___x_667_);
    return v___x_668_;
}
pub unsafe fn l_Lake_ModuleOutputDescrs_toJson(
    mut v_self_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_684_: u8 = 0;
    let mut v_ilean_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ir_x3f_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bc_x3f_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltar_x3f_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_obj_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_693_: u64 = 0;
    let mut v_ext_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u8 = 0;
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_718_: u64 = 0;
    let mut v_ext_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: u8 = 0;
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_obj_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_731_: u64 = 0;
    let mut v_ext_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_748_: u64 = 0;
    let mut v_ext_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_obj_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_obj_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_obj_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_764_: u64 = 0;
    let mut v_ext_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: u8 = 0;
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: u8 = 0;
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isModule_684_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_676_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                v_ilean_685_ = crate::leanh::lean_ctor_get(v_self_676_, 3);
                v_ir_x3f_686_ = crate::leanh::lean_ctor_get(v_self_676_, 4);
                crate::leanh::lean_inc(v_ir_x3f_686_);
                v_c_687_ = crate::leanh::lean_ctor_get(v_self_676_, 5);
                crate::leanh::lean_inc_ref(v_c_687_);
                v_bc_x3f_688_ = crate::leanh::lean_ctor_get(v_self_676_, 6);
                crate::leanh::lean_inc(v_bc_x3f_688_);
                v_ltar_x3f_689_ = crate::leanh::lean_ctor_get(v_self_676_, 7);
                crate::leanh::lean_inc(v_ltar_x3f_689_);
                v_hash_748_ = crate::leanh::lean_ctor_get_uint64(
                    v_ilean_685_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_ext_749_ = crate::leanh::lean_ctor_get(v_ilean_685_, 0);
                crate::leanh::lean_inc_ref(v_ext_749_);
                v_obj_750_ = crate::leanh::lean_box(1);
                v___x_751_ = l_Lake_ModuleOutputDescrs_toJson___closed__3;
                v___x_752_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_752_, 0 as u32, v_isModule_684_);
                v_obj_753_ = l_Lake_JsonObject_insertJson(v_obj_750_, v___x_751_, v___x_752_);
                v___x_754_ = l_Lake_ModuleOutputDescrs_toJson___closed__4;
                v___x_755_ = l_Lake_ModuleOutputDescrs_oleanParts(v_self_676_);
                v___x_756_ =
                    l_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(v___x_755_);
                v_obj_757_ = l_Lake_JsonObject_insertJson(v_obj_753_, v___x_754_, v___x_756_);
                v___x_758_ = l_Lake_ModuleOutputDescrs_toJson___closed__5;
                v___x_775_ = lean_string_utf8_byte_size(v_ext_749_);
                v___x_776_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_777_ = lean_nat_dec_eq(v___x_775_, v___x_776_);
                if v___x_777_ == 0 {
                    v___x_778_ = l_Lake_lowerHexUInt64(v_hash_748_);
                    v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                    v___x_780_ = lean_string_append(v___x_778_, v___x_779_);
                    v___x_781_ = lean_string_append(v___x_780_, v_ext_749_);
                    crate::leanh::lean_dec_ref(v_ext_749_);
                    v___y_760_ = v___x_781_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_ext_749_);
                    v___x_782_ = l_Lake_lowerHexUInt64(v_hash_748_);
                    v___y_760_ = v___x_782_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_681_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_681_, 0, v___y_680_);
                crate::leanh::lean_inc_ref(v___y_678_);
                v___x_682_ = l_Lake_JsonObject_insertJson(v___y_679_, v___y_678_, v___x_681_);
                v___x_683_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_683_, 0, v___x_682_);
                return v___x_683_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_ltar_x3f_689_) == 1 {
                    v_val_692_ = crate::leanh::lean_ctor_get(v_ltar_x3f_689_, 0);
                    crate::leanh::lean_inc(v_val_692_);
                    crate::leanh::lean_dec_ref_known(v_ltar_x3f_689_, 1);
                    v_hash_693_ = crate::leanh::lean_ctor_get_uint64(
                        v_val_692_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_ext_694_ = crate::leanh::lean_ctor_get(v_val_692_, 0);
                    crate::leanh::lean_inc_ref(v_ext_694_);
                    crate::leanh::lean_dec(v_val_692_);
                    v___x_695_ = l_Lake_ModuleOutputDescrs_toJson___closed__0;
                    v___x_696_ = lean_string_utf8_byte_size(v_ext_694_);
                    v___x_697_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_698_ = lean_nat_dec_eq(v___x_696_, v___x_697_);
                    if v___x_698_ == 0 {
                        v___x_699_ = l_Lake_lowerHexUInt64(v_hash_693_);
                        v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                        v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
                        v___x_702_ = lean_string_append(v___x_701_, v_ext_694_);
                        crate::leanh::lean_dec_ref(v_ext_694_);
                        v___y_678_ = v___x_695_;
                        v___y_679_ = v_obj_691_;
                        v___y_680_ = v___x_702_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_ext_694_);
                        v___x_703_ = l_Lake_lowerHexUInt64(v_hash_693_);
                        v___y_678_ = v___x_695_;
                        v___y_679_ = v_obj_691_;
                        v___y_680_ = v___x_703_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ltar_x3f_689_);
                    v___x_704_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_704_, 0, v_obj_691_);
                    return v___x_704_;
                }
            }
            3 => {
                v___x_709_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_709_, 0, v___y_708_);
                crate::leanh::lean_inc_ref(v___y_707_);
                v___x_710_ = l_Lake_JsonObject_insertJson(v___y_706_, v___y_707_, v___x_709_);
                v_obj_691_ = v___x_710_;
                state = 2;
                continue;
            }
            4 => {
                v___x_715_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_715_, 0, v___y_714_);
                crate::leanh::lean_inc_ref(v___y_712_);
                v___x_716_ = l_Lake_JsonObject_insertJson(v___y_713_, v___y_712_, v___x_715_);
                if crate::leanh::lean_obj_tag(v_bc_x3f_688_) == 1 {
                    v_val_717_ = crate::leanh::lean_ctor_get(v_bc_x3f_688_, 0);
                    crate::leanh::lean_inc(v_val_717_);
                    crate::leanh::lean_dec_ref_known(v_bc_x3f_688_, 1);
                    v_hash_718_ = crate::leanh::lean_ctor_get_uint64(
                        v_val_717_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_ext_719_ = crate::leanh::lean_ctor_get(v_val_717_, 0);
                    crate::leanh::lean_inc_ref(v_ext_719_);
                    crate::leanh::lean_dec(v_val_717_);
                    v___x_720_ = l_Lake_ModuleOutputDescrs_toJson___closed__1;
                    v___x_721_ = lean_string_utf8_byte_size(v_ext_719_);
                    v___x_722_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_723_ = lean_nat_dec_eq(v___x_721_, v___x_722_);
                    if v___x_723_ == 0 {
                        v___x_724_ = l_Lake_lowerHexUInt64(v_hash_718_);
                        v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                        v___x_726_ = lean_string_append(v___x_724_, v___x_725_);
                        v___x_727_ = lean_string_append(v___x_726_, v_ext_719_);
                        crate::leanh::lean_dec_ref(v_ext_719_);
                        v___y_706_ = v___x_716_;
                        v___y_707_ = v___x_720_;
                        v___y_708_ = v___x_727_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_ext_719_);
                        v___x_728_ = l_Lake_lowerHexUInt64(v_hash_718_);
                        v___y_706_ = v___x_716_;
                        v___y_707_ = v___x_720_;
                        v___y_708_ = v___x_728_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_bc_x3f_688_);
                    v_obj_691_ = v___x_716_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v_hash_731_ = crate::leanh::lean_ctor_get_uint64(
                    v_c_687_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_ext_732_ = crate::leanh::lean_ctor_get(v_c_687_, 0);
                crate::leanh::lean_inc_ref(v_ext_732_);
                crate::leanh::lean_dec_ref(v_c_687_);
                v___x_733_ = l_Lake_ModuleOutputDescrs_toJson___closed__2;
                v___x_734_ = lean_string_utf8_byte_size(v_ext_732_);
                v___x_735_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_736_ = lean_nat_dec_eq(v___x_734_, v___x_735_);
                if v___x_736_ == 0 {
                    v___x_737_ = l_Lake_lowerHexUInt64(v_hash_731_);
                    v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                    v___x_739_ = lean_string_append(v___x_737_, v___x_738_);
                    v___x_740_ = lean_string_append(v___x_739_, v_ext_732_);
                    crate::leanh::lean_dec_ref(v_ext_732_);
                    v___y_712_ = v___x_733_;
                    v___y_713_ = v_obj_730_;
                    v___y_714_ = v___x_740_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_ext_732_);
                    v___x_741_ = l_Lake_lowerHexUInt64(v_hash_731_);
                    v___y_712_ = v___x_733_;
                    v___y_713_ = v_obj_730_;
                    v___y_714_ = v___x_741_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_746_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_746_, 0, v___y_745_);
                crate::leanh::lean_inc_ref(v___y_744_);
                v___x_747_ = l_Lake_JsonObject_insertJson(v___y_743_, v___y_744_, v___x_746_);
                v_obj_730_ = v___x_747_;
                state = 5;
                continue;
            }
            7 => {
                v___x_761_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_761_, 0, v___y_760_);
                v___x_762_ = l_Lake_JsonObject_insertJson(v_obj_757_, v___x_758_, v___x_761_);
                if crate::leanh::lean_obj_tag(v_ir_x3f_686_) == 1 {
                    v_val_763_ = crate::leanh::lean_ctor_get(v_ir_x3f_686_, 0);
                    crate::leanh::lean_inc(v_val_763_);
                    crate::leanh::lean_dec_ref_known(v_ir_x3f_686_, 1);
                    v_hash_764_ = crate::leanh::lean_ctor_get_uint64(
                        v_val_763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_ext_765_ = crate::leanh::lean_ctor_get(v_val_763_, 0);
                    crate::leanh::lean_inc_ref(v_ext_765_);
                    crate::leanh::lean_dec(v_val_763_);
                    v___x_766_ = l_Lake_ModuleOutputDescrs_toJson___closed__6;
                    v___x_767_ = lean_string_utf8_byte_size(v_ext_765_);
                    v___x_768_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_769_ = lean_nat_dec_eq(v___x_767_, v___x_768_);
                    if v___x_769_ == 0 {
                        v___x_770_ = l_Lake_lowerHexUInt64(v_hash_764_);
                        v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                        v___x_772_ = lean_string_append(v___x_770_, v___x_771_);
                        v___x_773_ = lean_string_append(v___x_772_, v_ext_765_);
                        crate::leanh::lean_dec_ref(v_ext_765_);
                        v___y_743_ = v___x_762_;
                        v___y_744_ = v___x_766_;
                        v___y_745_ = v___x_773_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_ext_765_);
                        v___x_774_ = l_Lake_lowerHexUInt64(v_hash_764_);
                        v___y_743_ = v___x_762_;
                        v___y_744_ = v___x_766_;
                        v___y_745_ = v___x_774_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ir_x3f_686_);
                    v_obj_730_ = v___x_762_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(
    mut v_x_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_793_: u8 = 0;
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut v_a_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_801_: u8 = 0;
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_787_) == 0 {
                    v___x_788_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0;
                    return v___x_788_;
                } else {
                    v___x_789_ = l_Lake_ArtifactDescr_fromJson_x3f(v_x_787_);
                    if crate::leanh::lean_obj_tag(v___x_789_) == 0 {
                        v_a_790_ = crate::leanh::lean_ctor_get(v___x_789_, 0);
                        v_isSharedCheck_797_ = (!crate::leanh::lean_is_exclusive(v___x_789_)) as u8;
                        if v_isSharedCheck_797_ == 0 {
                            v___x_792_ = v___x_789_;
                            v_isShared_793_ = v_isSharedCheck_797_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_790_);
                            crate::leanh::lean_dec(v___x_789_);
                            v___x_792_ = crate::leanh::lean_box(0);
                            v_isShared_793_ = v_isSharedCheck_797_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_798_ = crate::leanh::lean_ctor_get(v___x_789_, 0);
                        v_isSharedCheck_806_ = (!crate::leanh::lean_is_exclusive(v___x_789_)) as u8;
                        if v_isSharedCheck_806_ == 0 {
                            v___x_800_ = v___x_789_;
                            v_isShared_801_ = v_isSharedCheck_806_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_798_);
                            crate::leanh::lean_dec(v___x_789_);
                            v___x_800_ = crate::leanh::lean_box(0);
                            v_isShared_801_ = v_isSharedCheck_806_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_793_ == 0 {
                    v___x_795_ = v___x_792_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_796_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
                    v___x_795_ = v_reuseFailAlloc_796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_795_;
            }
            3 => {
                v___x_802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_802_, 0, v_a_798_);
                if v_isShared_801_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_800_, 0, v___x_802_);
                    v___x_804_ = v___x_800_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
                    v___x_804_ = v_reuseFailAlloc_805_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(
    mut v_x_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_815_: u8 = 0;
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_819_: u8 = 0;
    let mut v_a_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_823_: u8 = 0;
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_809_) == 0 {
                    v___x_810_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0;
                    return v___x_810_;
                } else {
                    v___x_811_ = l_Lean_Json_getBool_x3f(v_x_809_);
                    if crate::leanh::lean_obj_tag(v___x_811_) == 0 {
                        v_a_812_ = crate::leanh::lean_ctor_get(v___x_811_, 0);
                        v_isSharedCheck_819_ = (!crate::leanh::lean_is_exclusive(v___x_811_)) as u8;
                        if v_isSharedCheck_819_ == 0 {
                            v___x_814_ = v___x_811_;
                            v_isShared_815_ = v_isSharedCheck_819_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_812_);
                            crate::leanh::lean_dec(v___x_811_);
                            v___x_814_ = crate::leanh::lean_box(0);
                            v_isShared_815_ = v_isSharedCheck_819_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_820_ = crate::leanh::lean_ctor_get(v___x_811_, 0);
                        v_isSharedCheck_828_ = (!crate::leanh::lean_is_exclusive(v___x_811_)) as u8;
                        if v_isSharedCheck_828_ == 0 {
                            v___x_822_ = v___x_811_;
                            v_isShared_823_ = v_isSharedCheck_828_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_820_);
                            crate::leanh::lean_dec(v___x_811_);
                            v___x_822_ = crate::leanh::lean_box(0);
                            v_isShared_823_ = v_isSharedCheck_828_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_815_ == 0 {
                    v___x_817_ = v___x_814_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
                    v___x_817_ = v_reuseFailAlloc_818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_817_;
            }
            3 => {
                v___x_824_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_824_, 0, v_a_820_);
                if v_isShared_823_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_822_, 0, v___x_824_);
                    v___x_826_ = v___x_822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_827_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
                    v___x_826_ = v_reuseFailAlloc_827_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___boxed(
    mut v_x_829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_830_ =
        l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_x_829_);
    crate::leanh::lean_dec(v_x_829_);
    return v_res_830_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(
    mut v_sz_831_: usize,
    mut v_i_832_: usize,
    mut v_bs_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_834_: u8 = 0;
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_845_: u8 = 0;
    let mut v_a_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: usize = 0;
    let mut v___x_850_: usize = 0;
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_834_ = lean_usize_dec_lt(v_i_832_, v_sz_831_);
                if v___x_834_ == 0 {
                    v___x_835_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_835_, 0, v_bs_833_);
                    return v___x_835_;
                } else {
                    v_v_836_ = lean_array_uget_borrowed(v_bs_833_, v_i_832_);
                    crate::leanh::lean_inc(v_v_836_);
                    v___x_837_ = l_Lake_ArtifactDescr_fromJson_x3f(v_v_836_);
                    if crate::leanh::lean_obj_tag(v___x_837_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_833_);
                        v_a_838_ = crate::leanh::lean_ctor_get(v___x_837_, 0);
                        v_isSharedCheck_845_ = (!crate::leanh::lean_is_exclusive(v___x_837_)) as u8;
                        if v_isSharedCheck_845_ == 0 {
                            v___x_840_ = v___x_837_;
                            v_isShared_841_ = v_isSharedCheck_845_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_838_);
                            crate::leanh::lean_dec(v___x_837_);
                            v___x_840_ = crate::leanh::lean_box(0);
                            v_isShared_841_ = v_isSharedCheck_845_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_846_ = crate::leanh::lean_ctor_get(v___x_837_, 0);
                        crate::leanh::lean_inc(v_a_846_);
                        crate::leanh::lean_dec_ref_known(v___x_837_, 1);
                        v___x_847_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_848_ = lean_array_uset(v_bs_833_, v_i_832_, v___x_847_);
                        v___x_849_ = 1usize;
                        v___x_850_ = lean_usize_add(v_i_832_, v___x_849_);
                        v___x_851_ = lean_array_uset(v_bs_x27_848_, v_i_832_, v_a_846_);
                        v_i_832_ = v___x_850_;
                        v_bs_833_ = v___x_851_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_841_ == 0 {
                    v___x_843_ = v___x_840_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_844_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
                    v___x_843_ = v_reuseFailAlloc_844_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0___boxed(
    mut v_sz_853_: *mut crate::leanh::LeanObject,
    mut v_i_854_: *mut crate::leanh::LeanObject,
    mut v_bs_855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_856_: usize = 0;
    let mut v_i_boxed_857_: usize = 0;
    let mut v_res_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_856_ = crate::leanh::lean_unbox_usize(v_sz_853_);
    crate::leanh::lean_dec(v_sz_853_);
    v_i_boxed_857_ = crate::leanh::lean_unbox_usize(v_i_854_);
    crate::leanh::lean_dec(v_i_854_);
    v_res_858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_boxed_856_, v_i_boxed_857_, v_bs_855_);
    return v_res_858_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(
    mut v_x_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_861_) == 4 {
        let mut v_elems_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_863_: usize = 0;
        let mut v___x_864_: usize = 0;
        let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_862_ = crate::leanh::lean_ctor_get(v_x_861_, 0);
        crate::leanh::lean_inc_ref(v_elems_862_);
        crate::leanh::lean_dec_ref_known(v_x_861_, 1);
        v_sz_863_ = lean_array_size(v_elems_862_);
        v___x_864_ = 0usize;
        v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_863_, v___x_864_, v_elems_862_);
        return v___x_865_;
    } else {
        let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_866_ =
            l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0;
        v___x_867_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_868_ = l_Lean_Json_pretty(v_x_861_, v___x_867_);
        v___x_869_ = lean_string_append(v___x_866_, v___x_868_);
        crate::leanh::lean_dec_ref(v___x_868_);
        v___x_870_ =
            l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1;
        v___x_871_ = lean_string_append(v___x_869_, v___x_870_);
        v___x_872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_872_, 0, v___x_871_);
        return v___x_872_;
    }
}
pub unsafe fn l_Lake_ModuleOutputDescrs_fromJson_x3f(
    mut v_val_892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_a_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_909_: u8 = 0;
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_914_: u8 = 0;
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_920_: u8 = 0;
    let mut v_a_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_924_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_928_: u8 = 0;
    let mut v_a_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_932_: u8 = 0;
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: u8 = 0;
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_942_: u8 = 0;
    let mut v___y_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_955_: u8 = 0;
    let mut v___y_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: u8 = 0;
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_972_: u8 = 0;
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v_val_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: u8 = 0;
    let mut v___y_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1009_: u8 = 0;
    let mut v_a_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1013_: u8 = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1017_: u8 = 0;
    let mut v_a_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1031_: u8 = 0;
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1037_: u8 = 0;
    let mut v_a_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1041_: u8 = 0;
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut v_a_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1061_: u8 = 0;
    let mut v_a_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1065_: u8 = 0;
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1069_: u8 = 0;
    let mut v_a_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1087_: u8 = 0;
    let mut v_a_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1091_: u8 = 0;
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1095_: u8 = 0;
    let mut v_a_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v_a_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1115_: u8 = 0;
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut v_a_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1129_: u8 = 0;
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1135_: u8 = 0;
    let mut v_a_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1139_: u8 = 0;
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1143_: u8 = 0;
    let mut v_a_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1145_: u8 = 0;
    let mut v_isSharedCheck_1146_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_893_ = l_Lean_Json_getObj_x3f(v_val_892_);
                if crate::leanh::lean_obj_tag(v___x_893_) == 0 {
                    v_a_894_ = crate::leanh::lean_ctor_get(v___x_893_, 0);
                    v_isSharedCheck_901_ = (!crate::leanh::lean_is_exclusive(v___x_893_)) as u8;
                    if v_isSharedCheck_901_ == 0 {
                        v___x_896_ = v___x_893_;
                        v_isShared_897_ = v_isSharedCheck_901_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_894_);
                        crate::leanh::lean_dec(v___x_893_);
                        v___x_896_ = crate::leanh::lean_box(0);
                        v_isShared_897_ = v_isSharedCheck_901_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_902_ = crate::leanh::lean_ctor_get(v___x_893_, 0);
                    crate::leanh::lean_inc(v_a_902_);
                    crate::leanh::lean_dec_ref_known(v___x_893_, 1);
                    v___x_903_ = l_Lake_ModuleOutputDescrs_toJson___closed__4;
                    v___x_904_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_903_);
                    if crate::leanh::lean_obj_tag(v___x_904_) == 0 {
                        crate::leanh::lean_dec(v_a_902_);
                        v___x_905_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1;
                        return v___x_905_;
                    } else {
                        v_val_906_ = crate::leanh::lean_ctor_get(v___x_904_, 0);
                        v_isSharedCheck_1146_ =
                            (!crate::leanh::lean_is_exclusive(v___x_904_)) as u8;
                        if v_isSharedCheck_1146_ == 0 {
                            v___x_908_ = v___x_904_;
                            v_isShared_909_ = v_isSharedCheck_1146_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_906_);
                            crate::leanh::lean_dec(v___x_904_);
                            v___x_908_ = crate::leanh::lean_box(0);
                            v_isShared_909_ = v_isSharedCheck_1146_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_897_ == 0 {
                    v___x_899_ = v___x_896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_900_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
                    v___x_899_ = v_reuseFailAlloc_900_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_899_;
            }
            3 => {
                v___x_910_ =
                    l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(
                        v_val_906_,
                    );
                if crate::leanh::lean_obj_tag(v___x_910_) == 0 {
                    crate::leanh::lean_del_object(v___x_908_);
                    crate::leanh::lean_dec(v_a_902_);
                    v_a_911_ = crate::leanh::lean_ctor_get(v___x_910_, 0);
                    v_isSharedCheck_920_ = (!crate::leanh::lean_is_exclusive(v___x_910_)) as u8;
                    if v_isSharedCheck_920_ == 0 {
                        v___x_913_ = v___x_910_;
                        v_isShared_914_ = v_isSharedCheck_920_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_911_);
                        crate::leanh::lean_dec(v___x_910_);
                        v___x_913_ = crate::leanh::lean_box(0);
                        v_isShared_914_ = v_isSharedCheck_920_;
                        state = 4;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_910_) == 0 {
                        crate::leanh::lean_del_object(v___x_908_);
                        crate::leanh::lean_dec(v_a_902_);
                        v_a_921_ = crate::leanh::lean_ctor_get(v___x_910_, 0);
                        v_isSharedCheck_928_ = (!crate::leanh::lean_is_exclusive(v___x_910_)) as u8;
                        if v_isSharedCheck_928_ == 0 {
                            v___x_923_ = v___x_910_;
                            v_isShared_924_ = v_isSharedCheck_928_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_921_);
                            crate::leanh::lean_dec(v___x_910_);
                            v___x_923_ = crate::leanh::lean_box(0);
                            v_isShared_924_ = v_isSharedCheck_928_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_929_ = crate::leanh::lean_ctor_get(v___x_910_, 0);
                        v_isSharedCheck_1145_ =
                            (!crate::leanh::lean_is_exclusive(v___x_910_)) as u8;
                        if v_isSharedCheck_1145_ == 0 {
                            v___x_931_ = v___x_910_;
                            v_isShared_932_ = v_isSharedCheck_1145_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_929_);
                            crate::leanh::lean_dec(v___x_910_);
                            v___x_931_ = crate::leanh::lean_box(0);
                            v_isShared_932_ = v_isSharedCheck_1145_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_915_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2;
                v___x_916_ = lean_string_append(v___x_915_, v_a_911_);
                crate::leanh::lean_dec(v_a_911_);
                if v_isShared_914_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_913_, 0, v___x_916_);
                    v___x_918_ = v___x_913_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_919_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
                    v___x_918_ = v_reuseFailAlloc_919_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_918_;
            }
            6 => {
                if v_isShared_924_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_923_, 0);
                    v___x_926_ = v___x_923_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_927_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
                    v___x_926_ = v_reuseFailAlloc_927_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_926_;
            }
            8 => {
                v___x_933_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_934_ = lean_array_get_size(v_a_929_);
                v___x_935_ = lean_nat_dec_lt(v___x_933_, v___x_934_);
                if v___x_935_ == 0 {
                    crate::leanh::lean_del_object(v___x_931_);
                    crate::leanh::lean_dec(v_a_929_);
                    crate::leanh::lean_del_object(v___x_908_);
                    crate::leanh::lean_dec(v_a_902_);
                    v___x_936_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4;
                    return v___x_936_;
                } else {
                    v___x_937_ = lean_array_fget(v_a_929_, v___x_933_);
                    v___x_1121_ = l_Lake_ModuleOutputDescrs_toJson___closed__3;
                    v___x_1122_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_1121_);
                    if crate::leanh::lean_obj_tag(v___x_1122_) == 0 {
                        v___x_1123_ = crate::leanh::lean_box(0);
                        v_a_1072_ = v___x_1123_;
                        state = 29;
                        continue;
                    } else {
                        v_val_1124_ = crate::leanh::lean_ctor_get(v___x_1122_, 0);
                        crate::leanh::lean_inc(v_val_1124_);
                        crate::leanh::lean_dec_ref_known(v___x_1122_, 1);
                        v___x_1125_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_val_1124_);
                        crate::leanh::lean_dec(v_val_1124_);
                        if crate::leanh::lean_obj_tag(v___x_1125_) == 0 {
                            crate::leanh::lean_dec(v___x_937_);
                            crate::leanh::lean_del_object(v___x_931_);
                            crate::leanh::lean_dec(v_a_929_);
                            crate::leanh::lean_del_object(v___x_908_);
                            crate::leanh::lean_dec(v_a_902_);
                            v_a_1126_ = crate::leanh::lean_ctor_get(v___x_1125_, 0);
                            v_isSharedCheck_1135_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1125_)) as u8;
                            if v_isSharedCheck_1135_ == 0 {
                                v___x_1128_ = v___x_1125_;
                                v_isShared_1129_ = v_isSharedCheck_1135_;
                                state = 38;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1126_);
                                crate::leanh::lean_dec(v___x_1125_);
                                v___x_1128_ = crate::leanh::lean_box(0);
                                v_isShared_1129_ = v_isSharedCheck_1135_;
                                state = 38;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_1125_) == 0 {
                                crate::leanh::lean_dec(v___x_937_);
                                crate::leanh::lean_del_object(v___x_931_);
                                crate::leanh::lean_dec(v_a_929_);
                                crate::leanh::lean_del_object(v___x_908_);
                                crate::leanh::lean_dec(v_a_902_);
                                v_a_1136_ = crate::leanh::lean_ctor_get(v___x_1125_, 0);
                                v_isSharedCheck_1143_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1125_)) as u8;
                                if v_isSharedCheck_1143_ == 0 {
                                    v___x_1138_ = v___x_1125_;
                                    v_isShared_1139_ = v_isSharedCheck_1143_;
                                    state = 40;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1136_);
                                    crate::leanh::lean_dec(v___x_1125_);
                                    v___x_1138_ = crate::leanh::lean_box(0);
                                    v_isShared_1139_ = v_isSharedCheck_1143_;
                                    state = 40;
                                    continue;
                                }
                            } else {
                                v_a_1144_ = crate::leanh::lean_ctor_get(v___x_1125_, 0);
                                crate::leanh::lean_inc(v_a_1144_);
                                crate::leanh::lean_dec_ref_known(v___x_1125_, 1);
                                v_a_1072_ = v_a_1144_;
                                state = 29;
                                continue;
                            }
                        }
                    }
                }
            }
            9 => {
                v___x_947_ = crate::leanh::lean_alloc_ctor(0, 8, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_947_, 0, v___x_937_);
                crate::leanh::lean_ctor_set(v___x_947_, 1, v___y_945_);
                crate::leanh::lean_ctor_set(v___x_947_, 2, v___y_946_);
                crate::leanh::lean_ctor_set(v___x_947_, 3, v___y_944_);
                crate::leanh::lean_ctor_set(v___x_947_, 4, v___y_940_);
                crate::leanh::lean_ctor_set(v___x_947_, 5, v___y_943_);
                crate::leanh::lean_ctor_set(v___x_947_, 6, v___y_939_);
                crate::leanh::lean_ctor_set(v___x_947_, 7, v___y_941_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_947_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    v___y_942_,
                );
                if v_isShared_932_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_931_, 0, v___x_947_);
                    v___x_949_ = v___x_931_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
                    v___x_949_ = v_reuseFailAlloc_950_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_949_;
            }
            11 => {
                v___x_959_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_960_ = lean_nat_dec_lt(v___x_959_, v___x_934_);
                if v___x_960_ == 0 {
                    crate::leanh::lean_dec(v_a_929_);
                    crate::leanh::lean_del_object(v___x_908_);
                    v___x_961_ = crate::leanh::lean_box(0);
                    v___y_939_ = v___y_952_;
                    v___y_940_ = v___y_953_;
                    v___y_941_ = v___y_954_;
                    v___y_942_ = v___y_955_;
                    v___y_943_ = v___y_956_;
                    v___y_944_ = v___y_957_;
                    v___y_945_ = v___y_958_;
                    v___y_946_ = v___x_961_;
                    state = 9;
                    continue;
                } else {
                    v___x_962_ = lean_array_fget(v_a_929_, v___x_959_);
                    crate::leanh::lean_dec(v_a_929_);
                    if v_isShared_909_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_908_, 0, v___x_962_);
                        v___x_964_ = v___x_908_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_965_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
                        v___x_964_ = v_reuseFailAlloc_965_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                v___y_939_ = v___y_952_;
                v___y_940_ = v___y_953_;
                v___y_941_ = v___y_954_;
                v___y_942_ = v___y_955_;
                v___y_943_ = v___y_956_;
                v___y_944_ = v___y_957_;
                v___y_945_ = v___y_958_;
                v___y_946_ = v___x_964_;
                state = 9;
                continue;
            }
            13 => {
                v___x_973_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_974_ = lean_nat_dec_lt(v___x_973_, v___x_934_);
                if v___x_974_ == 0 {
                    v___x_975_ = crate::leanh::lean_box(0);
                    v___y_952_ = v___y_967_;
                    v___y_953_ = v___y_968_;
                    v___y_954_ = v___y_969_;
                    v___y_955_ = v___y_972_;
                    v___y_956_ = v___y_970_;
                    v___y_957_ = v___y_971_;
                    v___y_958_ = v___x_975_;
                    state = 11;
                    continue;
                } else {
                    v___x_976_ = lean_array_fget_borrowed(v_a_929_, v___x_973_);
                    crate::leanh::lean_inc(v___x_976_);
                    v___x_977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_976_);
                    v___y_952_ = v___y_967_;
                    v___y_953_ = v___y_968_;
                    v___y_954_ = v___y_969_;
                    v___y_955_ = v___y_972_;
                    v___y_956_ = v___y_970_;
                    v___y_957_ = v___y_971_;
                    v___y_958_ = v___x_977_;
                    state = 11;
                    continue;
                }
            }
            14 => {
                if crate::leanh::lean_obj_tag(v___y_981_) == 0 {
                    v___x_985_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_986_ = lean_nat_dec_lt(v___x_985_, v___x_934_);
                    v___y_967_ = v___y_979_;
                    v___y_968_ = v___y_980_;
                    v___y_969_ = v_a_984_;
                    v___y_970_ = v___y_982_;
                    v___y_971_ = v___y_983_;
                    v___y_972_ = v___x_986_;
                    state = 13;
                    continue;
                } else {
                    v_val_987_ = crate::leanh::lean_ctor_get(v___y_981_, 0);
                    crate::leanh::lean_inc(v_val_987_);
                    crate::leanh::lean_dec_ref_known(v___y_981_, 1);
                    v___x_988_ = (crate::leanh::lean_unbox(v_val_987_) as u8);
                    crate::leanh::lean_dec(v_val_987_);
                    v___y_967_ = v___y_979_;
                    v___y_968_ = v___y_980_;
                    v___y_969_ = v_a_984_;
                    v___y_970_ = v___y_982_;
                    v___y_971_ = v___y_983_;
                    v___y_972_ = v___x_988_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_995_ = l_Lake_ModuleOutputDescrs_toJson___closed__0;
                v___x_996_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_995_);
                crate::leanh::lean_dec(v_a_902_);
                if crate::leanh::lean_obj_tag(v___x_996_) == 0 {
                    v___x_997_ = crate::leanh::lean_box(0);
                    v___y_979_ = v_a_994_;
                    v___y_980_ = v___y_990_;
                    v___y_981_ = v___y_991_;
                    v___y_982_ = v___y_992_;
                    v___y_983_ = v___y_993_;
                    v_a_984_ = v___x_997_;
                    state = 14;
                    continue;
                } else {
                    v_val_998_ = crate::leanh::lean_ctor_get(v___x_996_, 0);
                    crate::leanh::lean_inc(v_val_998_);
                    crate::leanh::lean_dec_ref_known(v___x_996_, 1);
                    v___x_999_ =
                        l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(
                            v_val_998_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_999_) == 0 {
                        crate::leanh::lean_dec(v_a_994_);
                        crate::leanh::lean_dec_ref(v___y_993_);
                        crate::leanh::lean_dec_ref(v___y_992_);
                        crate::leanh::lean_dec(v___y_991_);
                        crate::leanh::lean_dec(v___y_990_);
                        crate::leanh::lean_dec(v___x_937_);
                        crate::leanh::lean_del_object(v___x_931_);
                        crate::leanh::lean_dec(v_a_929_);
                        crate::leanh::lean_del_object(v___x_908_);
                        v_a_1000_ = crate::leanh::lean_ctor_get(v___x_999_, 0);
                        v_isSharedCheck_1009_ =
                            (!crate::leanh::lean_is_exclusive(v___x_999_)) as u8;
                        if v_isSharedCheck_1009_ == 0 {
                            v___x_1002_ = v___x_999_;
                            v_isShared_1003_ = v_isSharedCheck_1009_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1000_);
                            crate::leanh::lean_dec(v___x_999_);
                            v___x_1002_ = crate::leanh::lean_box(0);
                            v_isShared_1003_ = v_isSharedCheck_1009_;
                            state = 16;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_999_) == 0 {
                            crate::leanh::lean_dec(v_a_994_);
                            crate::leanh::lean_dec_ref(v___y_993_);
                            crate::leanh::lean_dec_ref(v___y_992_);
                            crate::leanh::lean_dec(v___y_991_);
                            crate::leanh::lean_dec(v___y_990_);
                            crate::leanh::lean_dec(v___x_937_);
                            crate::leanh::lean_del_object(v___x_931_);
                            crate::leanh::lean_dec(v_a_929_);
                            crate::leanh::lean_del_object(v___x_908_);
                            v_a_1010_ = crate::leanh::lean_ctor_get(v___x_999_, 0);
                            v_isSharedCheck_1017_ =
                                (!crate::leanh::lean_is_exclusive(v___x_999_)) as u8;
                            if v_isSharedCheck_1017_ == 0 {
                                v___x_1012_ = v___x_999_;
                                v_isShared_1013_ = v_isSharedCheck_1017_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1010_);
                                crate::leanh::lean_dec(v___x_999_);
                                v___x_1012_ = crate::leanh::lean_box(0);
                                v_isShared_1013_ = v_isSharedCheck_1017_;
                                state = 18;
                                continue;
                            }
                        } else {
                            v_a_1018_ = crate::leanh::lean_ctor_get(v___x_999_, 0);
                            crate::leanh::lean_inc(v_a_1018_);
                            crate::leanh::lean_dec_ref_known(v___x_999_, 1);
                            v___y_979_ = v_a_994_;
                            v___y_980_ = v___y_990_;
                            v___y_981_ = v___y_991_;
                            v___y_982_ = v___y_992_;
                            v___y_983_ = v___y_993_;
                            v_a_984_ = v_a_1018_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            16 => {
                v___x_1004_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5;
                v___x_1005_ = lean_string_append(v___x_1004_, v_a_1000_);
                crate::leanh::lean_dec(v_a_1000_);
                if v_isShared_1003_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1002_, 0, v___x_1005_);
                    v___x_1007_ = v___x_1002_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
                    v___x_1007_ = v_reuseFailAlloc_1008_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1007_;
            }
            18 => {
                if v_isShared_1013_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1012_, 0);
                    v___x_1015_ = v___x_1012_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1016_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
                    v___x_1015_ = v_reuseFailAlloc_1016_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1015_;
            }
            20 => {
                v___x_1023_ = l_Lake_ModuleOutputDescrs_toJson___closed__2;
                v___x_1024_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_1023_);
                if crate::leanh::lean_obj_tag(v___x_1024_) == 0 {
                    crate::leanh::lean_dec(v_a_1022_);
                    crate::leanh::lean_dec_ref(v___y_1021_);
                    crate::leanh::lean_dec(v___y_1020_);
                    crate::leanh::lean_dec(v___x_937_);
                    crate::leanh::lean_del_object(v___x_931_);
                    crate::leanh::lean_dec(v_a_929_);
                    crate::leanh::lean_del_object(v___x_908_);
                    crate::leanh::lean_dec(v_a_902_);
                    v___x_1025_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7;
                    return v___x_1025_;
                } else {
                    v_val_1026_ = crate::leanh::lean_ctor_get(v___x_1024_, 0);
                    crate::leanh::lean_inc(v_val_1026_);
                    crate::leanh::lean_dec_ref_known(v___x_1024_, 1);
                    v___x_1027_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_1026_);
                    if crate::leanh::lean_obj_tag(v___x_1027_) == 0 {
                        crate::leanh::lean_dec(v_a_1022_);
                        crate::leanh::lean_dec_ref(v___y_1021_);
                        crate::leanh::lean_dec(v___y_1020_);
                        crate::leanh::lean_dec(v___x_937_);
                        crate::leanh::lean_del_object(v___x_931_);
                        crate::leanh::lean_dec(v_a_929_);
                        crate::leanh::lean_del_object(v___x_908_);
                        crate::leanh::lean_dec(v_a_902_);
                        v_a_1028_ = crate::leanh::lean_ctor_get(v___x_1027_, 0);
                        v_isSharedCheck_1037_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1027_)) as u8;
                        if v_isSharedCheck_1037_ == 0 {
                            v___x_1030_ = v___x_1027_;
                            v_isShared_1031_ = v_isSharedCheck_1037_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1028_);
                            crate::leanh::lean_dec(v___x_1027_);
                            v___x_1030_ = crate::leanh::lean_box(0);
                            v_isShared_1031_ = v_isSharedCheck_1037_;
                            state = 21;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1027_) == 0 {
                            crate::leanh::lean_dec(v_a_1022_);
                            crate::leanh::lean_dec_ref(v___y_1021_);
                            crate::leanh::lean_dec(v___y_1020_);
                            crate::leanh::lean_dec(v___x_937_);
                            crate::leanh::lean_del_object(v___x_931_);
                            crate::leanh::lean_dec(v_a_929_);
                            crate::leanh::lean_del_object(v___x_908_);
                            crate::leanh::lean_dec(v_a_902_);
                            v_a_1038_ = crate::leanh::lean_ctor_get(v___x_1027_, 0);
                            v_isSharedCheck_1045_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1027_)) as u8;
                            if v_isSharedCheck_1045_ == 0 {
                                v___x_1040_ = v___x_1027_;
                                v_isShared_1041_ = v_isSharedCheck_1045_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1038_);
                                crate::leanh::lean_dec(v___x_1027_);
                                v___x_1040_ = crate::leanh::lean_box(0);
                                v_isShared_1041_ = v_isSharedCheck_1045_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_a_1046_ = crate::leanh::lean_ctor_get(v___x_1027_, 0);
                            crate::leanh::lean_inc(v_a_1046_);
                            crate::leanh::lean_dec_ref_known(v___x_1027_, 1);
                            v___x_1047_ = l_Lake_ModuleOutputDescrs_toJson___closed__1;
                            v___x_1048_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_1047_);
                            if crate::leanh::lean_obj_tag(v___x_1048_) == 0 {
                                v___x_1049_ = crate::leanh::lean_box(0);
                                v___y_990_ = v_a_1022_;
                                v___y_991_ = v___y_1020_;
                                v___y_992_ = v_a_1046_;
                                v___y_993_ = v___y_1021_;
                                v_a_994_ = v___x_1049_;
                                state = 15;
                                continue;
                            } else {
                                v_val_1050_ = crate::leanh::lean_ctor_get(v___x_1048_, 0);
                                crate::leanh::lean_inc(v_val_1050_);
                                crate::leanh::lean_dec_ref_known(v___x_1048_, 1);
                                v___x_1051_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_1050_);
                                if crate::leanh::lean_obj_tag(v___x_1051_) == 0 {
                                    crate::leanh::lean_dec(v_a_1046_);
                                    crate::leanh::lean_dec(v_a_1022_);
                                    crate::leanh::lean_dec_ref(v___y_1021_);
                                    crate::leanh::lean_dec(v___y_1020_);
                                    crate::leanh::lean_dec(v___x_937_);
                                    crate::leanh::lean_del_object(v___x_931_);
                                    crate::leanh::lean_dec(v_a_929_);
                                    crate::leanh::lean_del_object(v___x_908_);
                                    crate::leanh::lean_dec(v_a_902_);
                                    v_a_1052_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                                    v_isSharedCheck_1061_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                    if v_isSharedCheck_1061_ == 0 {
                                        v___x_1054_ = v___x_1051_;
                                        v_isShared_1055_ = v_isSharedCheck_1061_;
                                        state = 25;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1052_);
                                        crate::leanh::lean_dec(v___x_1051_);
                                        v___x_1054_ = crate::leanh::lean_box(0);
                                        v_isShared_1055_ = v_isSharedCheck_1061_;
                                        state = 25;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_1051_) == 0 {
                                        crate::leanh::lean_dec(v_a_1046_);
                                        crate::leanh::lean_dec(v_a_1022_);
                                        crate::leanh::lean_dec_ref(v___y_1021_);
                                        crate::leanh::lean_dec(v___y_1020_);
                                        crate::leanh::lean_dec(v___x_937_);
                                        crate::leanh::lean_del_object(v___x_931_);
                                        crate::leanh::lean_dec(v_a_929_);
                                        crate::leanh::lean_del_object(v___x_908_);
                                        crate::leanh::lean_dec(v_a_902_);
                                        v_a_1062_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                                        v_isSharedCheck_1069_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1051_)) as u8;
                                        if v_isSharedCheck_1069_ == 0 {
                                            v___x_1064_ = v___x_1051_;
                                            v_isShared_1065_ = v_isSharedCheck_1069_;
                                            state = 27;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1062_);
                                            crate::leanh::lean_dec(v___x_1051_);
                                            v___x_1064_ = crate::leanh::lean_box(0);
                                            v_isShared_1065_ = v_isSharedCheck_1069_;
                                            state = 27;
                                            continue;
                                        }
                                    } else {
                                        v_a_1070_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
                                        crate::leanh::lean_inc(v_a_1070_);
                                        crate::leanh::lean_dec_ref_known(v___x_1051_, 1);
                                        v___y_990_ = v_a_1022_;
                                        v___y_991_ = v___y_1020_;
                                        v___y_992_ = v_a_1046_;
                                        v___y_993_ = v___y_1021_;
                                        v_a_994_ = v_a_1070_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            21 => {
                v___x_1032_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8;
                v___x_1033_ = lean_string_append(v___x_1032_, v_a_1028_);
                crate::leanh::lean_dec(v_a_1028_);
                if v_isShared_1031_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1030_, 0, v___x_1033_);
                    v___x_1035_ = v___x_1030_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
                    v___x_1035_ = v_reuseFailAlloc_1036_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1035_;
            }
            23 => {
                if v_isShared_1041_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1040_, 0);
                    v___x_1043_ = v___x_1040_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1044_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
                    v___x_1043_ = v_reuseFailAlloc_1044_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1043_;
            }
            25 => {
                v___x_1056_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9;
                v___x_1057_ = lean_string_append(v___x_1056_, v_a_1052_);
                crate::leanh::lean_dec(v_a_1052_);
                if v_isShared_1055_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1054_, 0, v___x_1057_);
                    v___x_1059_ = v___x_1054_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
                    v___x_1059_ = v_reuseFailAlloc_1060_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1059_;
            }
            27 => {
                if v_isShared_1065_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1064_, 0);
                    v___x_1067_ = v___x_1064_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
                    v___x_1067_ = v_reuseFailAlloc_1068_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1067_;
            }
            29 => {
                v___x_1073_ = l_Lake_ModuleOutputDescrs_toJson___closed__5;
                v___x_1074_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_1073_);
                if crate::leanh::lean_obj_tag(v___x_1074_) == 0 {
                    crate::leanh::lean_dec(v_a_1072_);
                    crate::leanh::lean_dec(v___x_937_);
                    crate::leanh::lean_del_object(v___x_931_);
                    crate::leanh::lean_dec(v_a_929_);
                    crate::leanh::lean_del_object(v___x_908_);
                    crate::leanh::lean_dec(v_a_902_);
                    v___x_1075_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11;
                    return v___x_1075_;
                } else {
                    v_val_1076_ = crate::leanh::lean_ctor_get(v___x_1074_, 0);
                    crate::leanh::lean_inc(v_val_1076_);
                    crate::leanh::lean_dec_ref_known(v___x_1074_, 1);
                    v___x_1077_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_1076_);
                    if crate::leanh::lean_obj_tag(v___x_1077_) == 0 {
                        crate::leanh::lean_dec(v_a_1072_);
                        crate::leanh::lean_dec(v___x_937_);
                        crate::leanh::lean_del_object(v___x_931_);
                        crate::leanh::lean_dec(v_a_929_);
                        crate::leanh::lean_del_object(v___x_908_);
                        crate::leanh::lean_dec(v_a_902_);
                        v_a_1078_ = crate::leanh::lean_ctor_get(v___x_1077_, 0);
                        v_isSharedCheck_1087_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1077_)) as u8;
                        if v_isSharedCheck_1087_ == 0 {
                            v___x_1080_ = v___x_1077_;
                            v_isShared_1081_ = v_isSharedCheck_1087_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1078_);
                            crate::leanh::lean_dec(v___x_1077_);
                            v___x_1080_ = crate::leanh::lean_box(0);
                            v_isShared_1081_ = v_isSharedCheck_1087_;
                            state = 30;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1077_) == 0 {
                            crate::leanh::lean_dec(v_a_1072_);
                            crate::leanh::lean_dec(v___x_937_);
                            crate::leanh::lean_del_object(v___x_931_);
                            crate::leanh::lean_dec(v_a_929_);
                            crate::leanh::lean_del_object(v___x_908_);
                            crate::leanh::lean_dec(v_a_902_);
                            v_a_1088_ = crate::leanh::lean_ctor_get(v___x_1077_, 0);
                            v_isSharedCheck_1095_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1077_)) as u8;
                            if v_isSharedCheck_1095_ == 0 {
                                v___x_1090_ = v___x_1077_;
                                v_isShared_1091_ = v_isSharedCheck_1095_;
                                state = 32;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1088_);
                                crate::leanh::lean_dec(v___x_1077_);
                                v___x_1090_ = crate::leanh::lean_box(0);
                                v_isShared_1091_ = v_isSharedCheck_1095_;
                                state = 32;
                                continue;
                            }
                        } else {
                            v_a_1096_ = crate::leanh::lean_ctor_get(v___x_1077_, 0);
                            crate::leanh::lean_inc(v_a_1096_);
                            crate::leanh::lean_dec_ref_known(v___x_1077_, 1);
                            v___x_1097_ = l_Lake_ModuleOutputDescrs_toJson___closed__6;
                            v___x_1098_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_1097_);
                            if crate::leanh::lean_obj_tag(v___x_1098_) == 0 {
                                v___x_1099_ = crate::leanh::lean_box(0);
                                v___y_1020_ = v_a_1072_;
                                v___y_1021_ = v_a_1096_;
                                v_a_1022_ = v___x_1099_;
                                state = 20;
                                continue;
                            } else {
                                v_val_1100_ = crate::leanh::lean_ctor_get(v___x_1098_, 0);
                                crate::leanh::lean_inc(v_val_1100_);
                                crate::leanh::lean_dec_ref_known(v___x_1098_, 1);
                                v___x_1101_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_1100_);
                                if crate::leanh::lean_obj_tag(v___x_1101_) == 0 {
                                    crate::leanh::lean_dec(v_a_1096_);
                                    crate::leanh::lean_dec(v_a_1072_);
                                    crate::leanh::lean_dec(v___x_937_);
                                    crate::leanh::lean_del_object(v___x_931_);
                                    crate::leanh::lean_dec(v_a_929_);
                                    crate::leanh::lean_del_object(v___x_908_);
                                    crate::leanh::lean_dec(v_a_902_);
                                    v_a_1102_ = crate::leanh::lean_ctor_get(v___x_1101_, 0);
                                    v_isSharedCheck_1111_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1101_)) as u8;
                                    if v_isSharedCheck_1111_ == 0 {
                                        v___x_1104_ = v___x_1101_;
                                        v_isShared_1105_ = v_isSharedCheck_1111_;
                                        state = 34;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1102_);
                                        crate::leanh::lean_dec(v___x_1101_);
                                        v___x_1104_ = crate::leanh::lean_box(0);
                                        v_isShared_1105_ = v_isSharedCheck_1111_;
                                        state = 34;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_1101_) == 0 {
                                        crate::leanh::lean_dec(v_a_1096_);
                                        crate::leanh::lean_dec(v_a_1072_);
                                        crate::leanh::lean_dec(v___x_937_);
                                        crate::leanh::lean_del_object(v___x_931_);
                                        crate::leanh::lean_dec(v_a_929_);
                                        crate::leanh::lean_del_object(v___x_908_);
                                        crate::leanh::lean_dec(v_a_902_);
                                        v_a_1112_ = crate::leanh::lean_ctor_get(v___x_1101_, 0);
                                        v_isSharedCheck_1119_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1101_)) as u8;
                                        if v_isSharedCheck_1119_ == 0 {
                                            v___x_1114_ = v___x_1101_;
                                            v_isShared_1115_ = v_isSharedCheck_1119_;
                                            state = 36;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1112_);
                                            crate::leanh::lean_dec(v___x_1101_);
                                            v___x_1114_ = crate::leanh::lean_box(0);
                                            v_isShared_1115_ = v_isSharedCheck_1119_;
                                            state = 36;
                                            continue;
                                        }
                                    } else {
                                        v_a_1120_ = crate::leanh::lean_ctor_get(v___x_1101_, 0);
                                        crate::leanh::lean_inc(v_a_1120_);
                                        crate::leanh::lean_dec_ref_known(v___x_1101_, 1);
                                        v___y_1020_ = v_a_1072_;
                                        v___y_1021_ = v_a_1096_;
                                        v_a_1022_ = v_a_1120_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            30 => {
                v___x_1082_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12;
                v___x_1083_ = lean_string_append(v___x_1082_, v_a_1078_);
                crate::leanh::lean_dec(v_a_1078_);
                if v_isShared_1081_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1080_, 0, v___x_1083_);
                    v___x_1085_ = v___x_1080_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1086_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
                    v___x_1085_ = v_reuseFailAlloc_1086_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1085_;
            }
            32 => {
                if v_isShared_1091_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1090_, 0);
                    v___x_1093_ = v___x_1090_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1094_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
                    v___x_1093_ = v_reuseFailAlloc_1094_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1093_;
            }
            34 => {
                v___x_1106_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13;
                v___x_1107_ = lean_string_append(v___x_1106_, v_a_1102_);
                crate::leanh::lean_dec(v_a_1102_);
                if v_isShared_1105_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1104_, 0, v___x_1107_);
                    v___x_1109_ = v___x_1104_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
                    v___x_1109_ = v_reuseFailAlloc_1110_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_1109_;
            }
            36 => {
                if v_isShared_1115_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1114_, 0);
                    v___x_1117_ = v___x_1114_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
                    v___x_1117_ = v_reuseFailAlloc_1118_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1117_;
            }
            38 => {
                v___x_1130_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14;
                v___x_1131_ = lean_string_append(v___x_1130_, v_a_1126_);
                crate::leanh::lean_dec(v_a_1126_);
                if v_isShared_1129_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1128_, 0, v___x_1131_);
                    v___x_1133_ = v___x_1128_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
                    v___x_1133_ = v_reuseFailAlloc_1134_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_1133_;
            }
            40 => {
                if v_isShared_1139_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1138_, 0);
                    v___x_1141_ = v___x_1138_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1142_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
                    v___x_1141_ = v_reuseFailAlloc_1142_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ModuleOutputArtifacts_descrs(
    mut v_arts_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_olean_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_1151_: u8 = 0;
    let mut v_oleanServer_x3f_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oleanPrivate_x3f_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ilean_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ir_x3f_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bc_x3f_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltar_x3f_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v_descr_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v_descr_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1185_: u8 = 0;
    let mut v___y_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1196_: u8 = 0;
    let mut v_descr_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1202_: u8 = 0;
    let mut v___y_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1211_: u8 = 0;
    let mut v_descr_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut v___y_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v_descr_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1229_: u8 = 0;
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1234_: u8 = 0;
    let mut v_descr_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1239_: u8 = 0;
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_olean_1150_ = crate::leanh::lean_ctor_get(v_arts_1149_, 0);
                v_isModule_1151_ = crate::leanh::lean_ctor_get_uint8(
                    v_arts_1149_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                v_oleanServer_x3f_1152_ = crate::leanh::lean_ctor_get(v_arts_1149_, 1);
                v_oleanPrivate_x3f_1153_ = crate::leanh::lean_ctor_get(v_arts_1149_, 2);
                v_ilean_1154_ = crate::leanh::lean_ctor_get(v_arts_1149_, 3);
                v_ir_x3f_1155_ = crate::leanh::lean_ctor_get(v_arts_1149_, 4);
                v_c_1156_ = crate::leanh::lean_ctor_get(v_arts_1149_, 5);
                v_bc_x3f_1157_ = crate::leanh::lean_ctor_get(v_arts_1149_, 6);
                v_ltar_x3f_1158_ = crate::leanh::lean_ctor_get(v_arts_1149_, 7);
                v_isSharedCheck_1240_ = (!crate::leanh::lean_is_exclusive(v_arts_1149_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v___x_1160_ = v_arts_1149_;
                    v_isShared_1161_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ltar_x3f_1158_);
                    crate::leanh::lean_inc(v_bc_x3f_1157_);
                    crate::leanh::lean_inc(v_c_1156_);
                    crate::leanh::lean_inc(v_ir_x3f_1155_);
                    crate::leanh::lean_inc(v_ilean_1154_);
                    crate::leanh::lean_inc(v_oleanPrivate_x3f_1153_);
                    crate::leanh::lean_inc(v_oleanServer_x3f_1152_);
                    crate::leanh::lean_inc(v_olean_1150_);
                    crate::leanh::lean_dec(v_arts_1149_);
                    v___x_1160_ = crate::leanh::lean_box(0);
                    v_isShared_1161_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_descr_1162_ = crate::leanh::lean_ctor_get(v_olean_1150_, 0);
                crate::leanh::lean_inc_ref(v_descr_1162_);
                crate::leanh::lean_dec_ref(v_olean_1150_);
                if crate::leanh::lean_obj_tag(v_oleanServer_x3f_1152_) == 0 {
                    v___x_1230_ = crate::leanh::lean_box(0);
                    v___y_1219_ = v___x_1230_;
                    state = 13;
                    continue;
                } else {
                    v_val_1231_ = crate::leanh::lean_ctor_get(v_oleanServer_x3f_1152_, 0);
                    v_isSharedCheck_1239_ =
                        (!crate::leanh::lean_is_exclusive(v_oleanServer_x3f_1152_)) as u8;
                    if v_isSharedCheck_1239_ == 0 {
                        v___x_1233_ = v_oleanServer_x3f_1152_;
                        v_isShared_1234_ = v_isSharedCheck_1239_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1231_);
                        crate::leanh::lean_dec(v_oleanServer_x3f_1152_);
                        v___x_1233_ = crate::leanh::lean_box(0);
                        v_isShared_1234_ = v_isSharedCheck_1239_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_ltar_x3f_1158_) == 0 {
                    v___x_1170_ = crate::leanh::lean_box(0);
                    if v_isShared_1161_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1160_, 7, v___x_1170_);
                        crate::leanh::lean_ctor_set(v___x_1160_, 6, v___y_1169_);
                        crate::leanh::lean_ctor_set(v___x_1160_, 5, v___y_1165_);
                        crate::leanh::lean_ctor_set(v___x_1160_, 4, v___y_1164_);
                        crate::leanh::lean_ctor_set(v___x_1160_, 3, v___y_1168_);
                        crate::leanh::lean_ctor_set(v___x_1160_, 2, v___y_1166_);
                        crate::leanh::lean_ctor_set(v___x_1160_, 1, v___y_1167_);
                        crate::leanh::lean_ctor_set(v___x_1160_, 0, v_descr_1162_);
                        v___x_1172_ = v___x_1160_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1173_ = crate::leanh::lean_alloc_ctor(0, 8, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_descr_1162_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___y_1167_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1173_, 2, v___y_1166_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1173_, 3, v___y_1168_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1173_, 4, v___y_1164_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1173_, 5, v___y_1165_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1173_, 6, v___y_1169_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1173_, 7, v___x_1170_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1173_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                            v_isModule_1151_,
                        );
                        v___x_1172_ = v_reuseFailAlloc_1173_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_1174_ = crate::leanh::lean_ctor_get(v_ltar_x3f_1158_, 0);
                    v_isSharedCheck_1185_ =
                        (!crate::leanh::lean_is_exclusive(v_ltar_x3f_1158_)) as u8;
                    if v_isSharedCheck_1185_ == 0 {
                        v___x_1176_ = v_ltar_x3f_1158_;
                        v_isShared_1177_ = v_isSharedCheck_1185_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1174_);
                        crate::leanh::lean_dec(v_ltar_x3f_1158_);
                        v___x_1176_ = crate::leanh::lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1185_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1172_;
            }
            4 => {
                v_descr_1178_ = crate::leanh::lean_ctor_get(v_val_1174_, 0);
                crate::leanh::lean_inc_ref(v_descr_1178_);
                crate::leanh::lean_dec(v_val_1174_);
                if v_isShared_1177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1176_, 0, v_descr_1178_);
                    v___x_1180_ = v___x_1176_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_descr_1178_);
                    v___x_1180_ = v_reuseFailAlloc_1184_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1161_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1160_, 7, v___x_1180_);
                    crate::leanh::lean_ctor_set(v___x_1160_, 6, v___y_1169_);
                    crate::leanh::lean_ctor_set(v___x_1160_, 5, v___y_1165_);
                    crate::leanh::lean_ctor_set(v___x_1160_, 4, v___y_1164_);
                    crate::leanh::lean_ctor_set(v___x_1160_, 3, v___y_1168_);
                    crate::leanh::lean_ctor_set(v___x_1160_, 2, v___y_1166_);
                    crate::leanh::lean_ctor_set(v___x_1160_, 1, v___y_1167_);
                    crate::leanh::lean_ctor_set(v___x_1160_, 0, v_descr_1162_);
                    v___x_1182_ = v___x_1160_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1183_ = crate::leanh::lean_alloc_ctor(0, 8, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_descr_1162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___y_1167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 2, v___y_1166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 3, v___y_1168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 4, v___y_1164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 5, v___y_1165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 6, v___y_1169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1183_, 7, v___x_1180_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1183_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                        v_isModule_1151_,
                    );
                    v___x_1182_ = v_reuseFailAlloc_1183_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1182_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_bc_x3f_1157_) == 0 {
                    v_descr_1191_ = crate::leanh::lean_ctor_get(v_c_1156_, 0);
                    crate::leanh::lean_inc_ref(v_descr_1191_);
                    crate::leanh::lean_dec_ref(v_c_1156_);
                    v___x_1192_ = crate::leanh::lean_box(0);
                    v___y_1164_ = v___y_1190_;
                    v___y_1165_ = v_descr_1191_;
                    v___y_1166_ = v___y_1188_;
                    v___y_1167_ = v___y_1187_;
                    v___y_1168_ = v___y_1189_;
                    v___y_1169_ = v___x_1192_;
                    state = 2;
                    continue;
                } else {
                    v_val_1193_ = crate::leanh::lean_ctor_get(v_bc_x3f_1157_, 0);
                    v_isSharedCheck_1202_ =
                        (!crate::leanh::lean_is_exclusive(v_bc_x3f_1157_)) as u8;
                    if v_isSharedCheck_1202_ == 0 {
                        v___x_1195_ = v_bc_x3f_1157_;
                        v_isShared_1196_ = v_isSharedCheck_1202_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1193_);
                        crate::leanh::lean_dec(v_bc_x3f_1157_);
                        v___x_1195_ = crate::leanh::lean_box(0);
                        v_isShared_1196_ = v_isSharedCheck_1202_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v_descr_1197_ = crate::leanh::lean_ctor_get(v_c_1156_, 0);
                crate::leanh::lean_inc_ref(v_descr_1197_);
                crate::leanh::lean_dec_ref(v_c_1156_);
                v_descr_1198_ = crate::leanh::lean_ctor_get(v_val_1193_, 0);
                crate::leanh::lean_inc_ref(v_descr_1198_);
                crate::leanh::lean_dec(v_val_1193_);
                if v_isShared_1196_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1195_, 0, v_descr_1198_);
                    v___x_1200_ = v___x_1195_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1201_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_descr_1198_);
                    v___x_1200_ = v_reuseFailAlloc_1201_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_1164_ = v___y_1190_;
                v___y_1165_ = v_descr_1197_;
                v___y_1166_ = v___y_1188_;
                v___y_1167_ = v___y_1187_;
                v___y_1168_ = v___y_1189_;
                v___y_1169_ = v___x_1200_;
                state = 2;
                continue;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_ir_x3f_1155_) == 0 {
                    v_descr_1206_ = crate::leanh::lean_ctor_get(v_ilean_1154_, 0);
                    crate::leanh::lean_inc_ref(v_descr_1206_);
                    crate::leanh::lean_dec_ref(v_ilean_1154_);
                    v___x_1207_ = crate::leanh::lean_box(0);
                    v___y_1187_ = v___y_1204_;
                    v___y_1188_ = v___y_1205_;
                    v___y_1189_ = v_descr_1206_;
                    v___y_1190_ = v___x_1207_;
                    state = 7;
                    continue;
                } else {
                    v_val_1208_ = crate::leanh::lean_ctor_get(v_ir_x3f_1155_, 0);
                    v_isSharedCheck_1217_ =
                        (!crate::leanh::lean_is_exclusive(v_ir_x3f_1155_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1210_ = v_ir_x3f_1155_;
                        v_isShared_1211_ = v_isSharedCheck_1217_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1208_);
                        crate::leanh::lean_dec(v_ir_x3f_1155_);
                        v___x_1210_ = crate::leanh::lean_box(0);
                        v_isShared_1211_ = v_isSharedCheck_1217_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                v_descr_1212_ = crate::leanh::lean_ctor_get(v_ilean_1154_, 0);
                crate::leanh::lean_inc_ref(v_descr_1212_);
                crate::leanh::lean_dec_ref(v_ilean_1154_);
                v_descr_1213_ = crate::leanh::lean_ctor_get(v_val_1208_, 0);
                crate::leanh::lean_inc_ref(v_descr_1213_);
                crate::leanh::lean_dec(v_val_1208_);
                if v_isShared_1211_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1210_, 0, v_descr_1213_);
                    v___x_1215_ = v___x_1210_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_descr_1213_);
                    v___x_1215_ = v_reuseFailAlloc_1216_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_1187_ = v___y_1204_;
                v___y_1188_ = v___y_1205_;
                v___y_1189_ = v_descr_1212_;
                v___y_1190_ = v___x_1215_;
                state = 7;
                continue;
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_oleanPrivate_x3f_1153_) == 0 {
                    v___x_1220_ = crate::leanh::lean_box(0);
                    v___y_1204_ = v___y_1219_;
                    v___y_1205_ = v___x_1220_;
                    state = 10;
                    continue;
                } else {
                    v_val_1221_ = crate::leanh::lean_ctor_get(v_oleanPrivate_x3f_1153_, 0);
                    v_isSharedCheck_1229_ =
                        (!crate::leanh::lean_is_exclusive(v_oleanPrivate_x3f_1153_)) as u8;
                    if v_isSharedCheck_1229_ == 0 {
                        v___x_1223_ = v_oleanPrivate_x3f_1153_;
                        v_isShared_1224_ = v_isSharedCheck_1229_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1221_);
                        crate::leanh::lean_dec(v_oleanPrivate_x3f_1153_);
                        v___x_1223_ = crate::leanh::lean_box(0);
                        v_isShared_1224_ = v_isSharedCheck_1229_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                v_descr_1225_ = crate::leanh::lean_ctor_get(v_val_1221_, 0);
                crate::leanh::lean_inc_ref(v_descr_1225_);
                crate::leanh::lean_dec(v_val_1221_);
                if v_isShared_1224_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1223_, 0, v_descr_1225_);
                    v___x_1227_ = v___x_1223_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_descr_1225_);
                    v___x_1227_ = v_reuseFailAlloc_1228_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_1204_ = v___y_1219_;
                v___y_1205_ = v___x_1227_;
                state = 10;
                continue;
            }
            16 => {
                v_descr_1235_ = crate::leanh::lean_ctor_get(v_val_1231_, 0);
                crate::leanh::lean_inc_ref(v_descr_1235_);
                crate::leanh::lean_dec(v_val_1231_);
                if v_isShared_1234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1233_, 0, v_descr_1235_);
                    v___x_1237_ = v___x_1233_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_descr_1235_);
                    v___x_1237_ = v_reuseFailAlloc_1238_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_1219_ = v___x_1237_;
                state = 13;
                continue;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_ModuleArtifacts(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Artifact(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_ModuleArtifacts(
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
pub unsafe fn initialize_Lake_Build_ModuleArtifacts(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Artifact(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_JsonObject(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_ModuleArtifacts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_ModuleArtifacts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_ModuleArtifacts(builtin);
}

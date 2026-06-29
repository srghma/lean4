// Lean compiler output
// Module: Lake.Reservoir
// Imports: Init.Control.Do Lake.Util.JsonObject Lake.Util.Version Lake.Config.Env Lake.Util.Reservoir Lake.Util.Url
use crate::r#gen::Init::Control::Do::{
    initialize_Init_Control_Do, runtime_initialize_Init_Control_Do,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toString, l_String_Slice_trimAscii};
use crate::r#gen::Lake::Config::Env::{
    initialize_Lake_Config_Env, runtime_initialize_Lake_Config_Env,
};
use crate::r#gen::Lake::Util::JsonObject::{
    initialize_Lake_Util_JsonObject, l_Lake_JsonObject_getJson_x3f,
    runtime_initialize_Lake_Util_JsonObject,
};
use crate::r#gen::Lake::Util::Reservoir::{
    initialize_Lake_Util_Reservoir, l_Lake_Reservoir_lakeHeaders,
    runtime_initialize_Lake_Util_Reservoir,
};
use crate::r#gen::Lake::Util::Url::{
    initialize_Lake_Util_Url, l_Lake_getUrl, l_Lake_uriEncode, runtime_initialize_Lake_Util_Url,
};
use crate::r#gen::Lake::Util::Version::{
    initialize_Lake_Util_Version, l_Lake_StdVer_parse, runtime_initialize_Lake_Util_Version,
};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getNat_x3f, l_Lean_Json_getObj_x3f, l_Lean_Json_getStr_x3f,
};
use crate::r#gen::Lean::Data::Json::Parser::l_Lean_Json_parse;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_string_append;
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_nat_dec_eq, lean_string_dec_eq,
    lean_string_utf8_byte_size,
};
pub static l_Lake_instInhabitedRegistrySrc_default___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lake_instInhabitedRegistrySrc_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedRegistrySrc_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedRegistrySrc_default___closed__1_value: crate::leanh::LeanCtorObject<
    5,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedRegistrySrc_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedRegistrySrc_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedRegistrySrc_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedRegistrySrc_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedRegistrySrc_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedRegistrySrc: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedRegistrySrc_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_instToJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_RegistrySrc_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_RegistrySrc_instToJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_instToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_RegistrySrc_instToJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_instToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
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
            105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 103, 105, 115, 116, 114, 121, 32, 115,
            111, 117, 114, 99, 101, 58, 32, 0,
        ],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [103, 105, 116, 85, 114, 108, 0],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__2_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 105, 116, 85, 114, 108, 58, 32, 0],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__3_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [115, 117, 98, 68, 105, 114, 0],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__4_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [115, 117, 98, 68, 105, 114, 58, 32, 0],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__5_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
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
            100, 101, 102, 97, 117, 108, 116, 66, 114, 97, 110, 99, 104, 0,
        ],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__6_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
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
            100, 101, 102, 97, 117, 108, 116, 66, 114, 97, 110, 99, 104, 58, 32, 0,
        ],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__7_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [104, 111, 115, 116, 0],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__8_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [104, 111, 115, 116, 58, 32, 0],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__9_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [103, 105, 116, 104, 117, 98, 0],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__10_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [114, 101, 112, 111, 85, 114, 108, 0],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_fromJson_x3f___closed__11_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [114, 101, 112, 111, 85, 114, 108, 58, 32, 0],
    };
static mut l_Lake_RegistrySrc_fromJson_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_fromJson_x3f___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistrySrc_instFromJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_RegistrySrc_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_RegistrySrc_instFromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_RegistrySrc_instFromJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistrySrc_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedRegistryPkg_default___closed__0_value:
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
static mut l_Lake_instInhabitedRegistryPkg_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedRegistryPkg_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedRegistryPkg_default___closed__1_value: crate::leanh::LeanCtorObject<
    4,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedRegistrySrc_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedRegistrySrc_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedRegistryPkg_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedRegistryPkg_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedRegistryPkg_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedRegistryPkg_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedRegistryPkg_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedRegistryPkg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedRegistryPkg_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0_value:
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
    m_fun: l_Lake_RegistryPkg_toJson___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Reservoir_0__Lake_RegistryPkg_instToJson___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_fromJson_x3f___closed__0_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 103, 105, 115, 116, 114, 121, 32, 112,
            97, 99, 107, 97, 103, 101, 58, 32, 0,
        ],
    };
static mut l_Lake_RegistryPkg_fromJson_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_fromJson_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_fromJson_x3f___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lake_RegistryPkg_fromJson_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_fromJson_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_fromJson_x3f___closed__2_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lake_RegistryPkg_fromJson_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_fromJson_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_fromJson_x3f___closed__3_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [110, 97, 109, 101, 58, 32, 0],
    };
static mut l_Lake_RegistryPkg_fromJson_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_fromJson_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_fromJson_x3f___closed__4_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [102, 117, 108, 108, 78, 97, 109, 101, 0],
    };
static mut l_Lake_RegistryPkg_fromJson_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_fromJson_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_fromJson_x3f___closed__5_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 102, 117, 108, 108, 78, 97, 109, 101, 0,
        ],
    };
static mut l_Lake_RegistryPkg_fromJson_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_fromJson_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_fromJson_x3f___closed__6_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [102, 117, 108, 108, 78, 97, 109, 101, 58, 32, 0],
    };
static mut l_Lake_RegistryPkg_fromJson_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_fromJson_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_fromJson_x3f___closed__7_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_RegistryPkg_fromJson_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_fromJson_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_fromJson_x3f___closed__8_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [115, 111, 117, 114, 99, 101, 115, 0],
    };
static mut l_Lake_RegistryPkg_fromJson_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_fromJson_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_fromJson_x3f___closed__9_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 111, 117, 114, 99, 101, 115, 58, 32, 0],
    };
static mut l_Lake_RegistryPkg_fromJson_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_fromJson_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryPkg_instFromJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_RegistryPkg_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_RegistryPkg_instFromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_RegistryPkg_instFromJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryPkg_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Reservoir_pkgApiUrl___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [47, 112, 97, 99, 107, 97, 103, 101, 115, 47, 0],
    };
static mut l_Lake_Reservoir_pkgApiUrl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_pkgApiUrl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Reservoir_pkgApiUrl___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [47, 0],
    };
static mut l_Lake_Reservoir_pkgApiUrl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_pkgApiUrl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 97, 116, 97, 0]};
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 114, 114, 111, 114, 0]};
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 114, 114, 111, 114, 58, 32, 0]};
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 116, 97, 116, 117, 115, 0]};
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__4_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58, 32, 115, 116, 97, 116, 117, 115, 0]};
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 116, 97, 116, 117, 115, 58, 32, 0]};
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 101, 115, 115, 97, 103, 101, 0]};
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__8_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58, 32, 109, 101, 115, 115, 97, 103, 101, 0]};
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 101, 115, 115, 97, 103, 101, 58, 32, 0]};
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Reservoir_fetchPkg_x3f___closed__0_value: crate::leanh::LeanStringObject<58> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 58,
        m_capacity: 58,
        m_length: 57,
        m_data: [
            58, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 32, 108, 111, 111, 107, 117, 112,
            32, 102, 97, 105, 108, 101, 100, 59, 32, 115, 101, 114, 118, 101, 114, 32, 114, 101,
            116, 117, 114, 110, 101, 100, 32, 105, 110, 118, 97, 108, 105, 100, 32, 74, 83, 79, 78,
            58, 32, 0,
        ],
    };
static mut l_Lake_Reservoir_fetchPkg_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_fetchPkg_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Reservoir_fetchPkg_x3f___closed__1_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            58, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 32, 114, 101, 115, 112, 111, 110,
            100, 101, 100, 32, 119, 105, 116, 104, 58, 10, 0,
        ],
    };
static mut l_Lake_Reservoir_fetchPkg_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_fetchPkg_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Reservoir_fetchPkg_x3f___closed__2_value: crate::leanh::LeanStringObject<62> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 62,
        m_capacity: 62,
        m_length: 61,
        m_data: [
            58, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 32, 108, 111, 111, 107, 117, 112,
            32, 102, 97, 105, 108, 101, 100, 59, 32, 115, 101, 114, 118, 101, 114, 32, 114, 101,
            116, 117, 114, 110, 101, 100, 32, 117, 110, 115, 117, 112, 112, 111, 114, 116, 101,
            100, 32, 74, 83, 79, 78, 58, 32, 0,
        ],
    };
static mut l_Lake_Reservoir_fetchPkg_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_fetchPkg_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Reservoir_fetchPkg_x3f___closed__3_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
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
            58, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 32, 108, 111, 111, 107, 117, 112,
            32, 102, 97, 105, 108, 101, 100, 58, 32, 0,
        ],
    };
static mut l_Lake_Reservoir_fetchPkg_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_fetchPkg_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Reservoir_fetchPkg_x3f___closed__4_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
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
            58, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 32, 108, 111, 111, 107, 117, 112,
            32, 102, 97, 105, 108, 101, 100, 0,
        ],
    };
static mut l_Lake_Reservoir_fetchPkg_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_fetchPkg_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryVer_fromJson_x3f___closed__0_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 103, 105, 115, 116, 114, 121, 32, 118,
            101, 114, 115, 105, 111, 110, 58, 32, 0,
        ],
    };
static mut l_Lake_RegistryVer_fromJson_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryVer_fromJson_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryVer_fromJson_x3f___closed__1_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [118, 101, 114, 115, 105, 111, 110, 58, 32, 0],
    };
static mut l_Lake_RegistryVer_fromJson_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryVer_fromJson_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryVer_fromJson_x3f___closed__2_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [118, 101, 114, 115, 105, 111, 110, 0],
    };
static mut l_Lake_RegistryVer_fromJson_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryVer_fromJson_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryVer_fromJson_x3f___closed__3_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 118, 101, 114, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Lake_RegistryVer_fromJson_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryVer_fromJson_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryVer_fromJson_x3f___closed__4_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [114, 101, 118, 105, 115, 105, 111, 110, 0],
    };
static mut l_Lake_RegistryVer_fromJson_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryVer_fromJson_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryVer_fromJson_x3f___closed__5_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 114, 101, 118, 105, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Lake_RegistryVer_fromJson_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryVer_fromJson_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_RegistryVer_fromJson_x3f___closed__6_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [114, 101, 118, 105, 115, 105, 111, 110, 58, 32, 0],
    };
static mut l_Lake_RegistryVer_fromJson_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_RegistryVer_fromJson_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instFromJsonRegistryVer___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_RegistryVer_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instFromJsonRegistryVer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonRegistryVer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instFromJsonRegistryVer: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonRegistryVer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Reservoir_pkgVersionsApiUrl___closed__0_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [47, 118, 101, 114, 115, 105, 111, 110, 115, 0],
};
static mut l_Lake_Reservoir_pkgVersionsApiUrl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_pkgVersionsApiUrl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Reservoir_fetchPkgVersions___closed__0_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            58, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 32, 108, 111, 111, 107, 117, 112,
            32, 102, 97, 105, 108, 101, 100, 32, 40, 99, 111, 100, 101, 58, 32, 0,
        ],
    };
static mut l_Lake_Reservoir_fetchPkgVersions___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_fetchPkgVersions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Reservoir_fetchPkgVersions___closed__1_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [41, 58, 32, 0],
    };
static mut l_Lake_Reservoir_fetchPkgVersions___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_fetchPkgVersions___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_RegistrySrc_ctorIdx(
    mut v_x_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1141_) == 0 {
        let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1142_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1142_;
    } else {
        let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1143_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1143_;
    }
}
pub unsafe fn l_Lake_RegistrySrc_ctorIdx___boxed(
    mut v_x_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1145_ = l_Lake_RegistrySrc_ctorIdx(v_x_1144_);
    crate::leanh::lean_dec_ref(v_x_1144_);
    return v_res_1145_;
}
pub unsafe fn l_Lake_RegistrySrc_ctorElim___redArg(
    mut v_t_1146_: *mut crate::leanh::LeanObject,
    mut v_k_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1146_) == 0 {
        let mut v_data_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_url_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_githubUrl_x3f_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_defaultBranch_x3f_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_subDir_x3f_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_data_1148_ = crate::leanh::lean_ctor_get(v_t_1146_, 0);
        crate::leanh::lean_inc(v_data_1148_);
        v_url_1149_ = crate::leanh::lean_ctor_get(v_t_1146_, 1);
        crate::leanh::lean_inc_ref(v_url_1149_);
        v_githubUrl_x3f_1150_ = crate::leanh::lean_ctor_get(v_t_1146_, 2);
        crate::leanh::lean_inc(v_githubUrl_x3f_1150_);
        v_defaultBranch_x3f_1151_ = crate::leanh::lean_ctor_get(v_t_1146_, 3);
        crate::leanh::lean_inc(v_defaultBranch_x3f_1151_);
        v_subDir_x3f_1152_ = crate::leanh::lean_ctor_get(v_t_1146_, 4);
        crate::leanh::lean_inc(v_subDir_x3f_1152_);
        crate::leanh::lean_dec_ref_known(v_t_1146_, 5);
        v___x_1153_ = crate::leanh::lean_apply_5(
            v_k_1147_,
            v_data_1148_,
            v_url_1149_,
            v_githubUrl_x3f_1150_,
            v_defaultBranch_x3f_1151_,
            v_subDir_x3f_1152_,
        );
        return v___x_1153_;
    } else {
        let mut v_data_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_data_1154_ = crate::leanh::lean_ctor_get(v_t_1146_, 0);
        crate::leanh::lean_inc(v_data_1154_);
        crate::leanh::lean_dec_ref_known(v_t_1146_, 1);
        v___x_1155_ = crate::leanh::lean_apply_1(v_k_1147_, v_data_1154_);
        return v___x_1155_;
    }
}
pub unsafe fn l_Lake_RegistrySrc_ctorElim(
    mut v_motive_1156_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1157_: *mut crate::leanh::LeanObject,
    mut v_t_1158_: *mut crate::leanh::LeanObject,
    mut v_h_1159_: *mut crate::leanh::LeanObject,
    mut v_k_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_1158_, v_k_1160_);
    return v___x_1161_;
}
pub unsafe fn l_Lake_RegistrySrc_ctorElim___boxed(
    mut v_motive_1162_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1163_: *mut crate::leanh::LeanObject,
    mut v_t_1164_: *mut crate::leanh::LeanObject,
    mut v_h_1165_: *mut crate::leanh::LeanObject,
    mut v_k_1166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1167_ = l_Lake_RegistrySrc_ctorElim(
        v_motive_1162_,
        v_ctorIdx_1163_,
        v_t_1164_,
        v_h_1165_,
        v_k_1166_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1163_);
    return v_res_1167_;
}
pub unsafe fn l_Lake_RegistrySrc_git_elim___redArg(
    mut v_t_1168_: *mut crate::leanh::LeanObject,
    mut v_git_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_1168_, v_git_1169_);
    return v___x_1170_;
}
pub unsafe fn l_Lake_RegistrySrc_git_elim(
    mut v_motive_1171_: *mut crate::leanh::LeanObject,
    mut v_t_1172_: *mut crate::leanh::LeanObject,
    mut v_h_1173_: *mut crate::leanh::LeanObject,
    mut v_git_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_1172_, v_git_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Lake_RegistrySrc_other_elim___redArg(
    mut v_t_1176_: *mut crate::leanh::LeanObject,
    mut v_other_1177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_1176_, v_other_1177_);
    return v___x_1178_;
}
pub unsafe fn l_Lake_RegistrySrc_other_elim(
    mut v_motive_1179_: *mut crate::leanh::LeanObject,
    mut v_t_1180_: *mut crate::leanh::LeanObject,
    mut v_h_1181_: *mut crate::leanh::LeanObject,
    mut v_other_1182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1183_ = l_Lake_RegistrySrc_ctorElim___redArg(v_t_1180_, v_other_1182_);
    return v___x_1183_;
}
pub unsafe fn l_Lake_RegistrySrc_isGit(mut v_src_1191_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_src_1191_) == 0 {
        let mut v___x_1192_: u8 = 0;
        v___x_1192_ = 1;
        return v___x_1192_;
    } else {
        let mut v___x_1193_: u8 = 0;
        v___x_1193_ = 0;
        return v___x_1193_;
    }
}
pub unsafe fn l_Lake_RegistrySrc_isGit___boxed(
    mut v_src_1194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1195_: u8 = 0;
    let mut v_r_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1195_ = l_Lake_RegistrySrc_isGit(v_src_1194_);
    crate::leanh::lean_dec_ref(v_src_1194_);
    v_r_1196_ = crate::leanh::lean_box((v_res_1195_) as usize);
    return v_r_1196_;
}
pub unsafe fn l_Lake_RegistrySrc_data(
    mut v_src_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_data_1198_ = crate::leanh::lean_ctor_get(v_src_1197_, 0);
    crate::leanh::lean_inc(v_data_1198_);
    return v_data_1198_;
}
pub unsafe fn l_Lake_RegistrySrc_data___boxed(
    mut v_src_1199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1200_ = l_Lake_RegistrySrc_data(v_src_1199_);
    crate::leanh::lean_dec_ref(v_src_1199_);
    return v_res_1200_;
}
pub unsafe fn l_Lake_RegistrySrc_toJson(
    mut v_src_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1207_: u8 = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_src_1201_) == 0 {
                    v_data_1202_ = crate::leanh::lean_ctor_get(v_src_1201_, 0);
                    crate::leanh::lean_inc(v_data_1202_);
                    crate::leanh::lean_dec_ref_known(v_src_1201_, 5);
                    v___x_1203_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1203_, 0, v_data_1202_);
                    return v___x_1203_;
                } else {
                    v_data_1204_ = crate::leanh::lean_ctor_get(v_src_1201_, 0);
                    v_isSharedCheck_1211_ = (!crate::leanh::lean_is_exclusive(v_src_1201_)) as u8;
                    if v_isSharedCheck_1211_ == 0 {
                        v___x_1206_ = v_src_1201_;
                        v_isShared_1207_ = v_isSharedCheck_1211_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_data_1204_);
                        crate::leanh::lean_dec(v_src_1201_);
                        v___x_1206_ = crate::leanh::lean_box(0);
                        v_isShared_1207_ = v_isSharedCheck_1211_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1207_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1206_, 5);
                    v___x_1209_ = v___x_1206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1210_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_data_1204_);
                    v___x_1209_ = v_reuseFailAlloc_1210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(
    mut v_x_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut v_a_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1216_) == 0 {
                    v___x_1217_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0;
                    return v___x_1217_;
                } else {
                    v___x_1218_ = l_Lean_Json_getStr_x3f(v_x_1216_);
                    if crate::leanh::lean_obj_tag(v___x_1218_) == 0 {
                        v_a_1219_ = crate::leanh::lean_ctor_get(v___x_1218_, 0);
                        v_isSharedCheck_1226_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1218_)) as u8;
                        if v_isSharedCheck_1226_ == 0 {
                            v___x_1221_ = v___x_1218_;
                            v_isShared_1222_ = v_isSharedCheck_1226_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1219_);
                            crate::leanh::lean_dec(v___x_1218_);
                            v___x_1221_ = crate::leanh::lean_box(0);
                            v_isShared_1222_ = v_isSharedCheck_1226_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1227_ = crate::leanh::lean_ctor_get(v___x_1218_, 0);
                        v_isSharedCheck_1235_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1218_)) as u8;
                        if v_isSharedCheck_1235_ == 0 {
                            v___x_1229_ = v___x_1218_;
                            v_isShared_1230_ = v_isSharedCheck_1235_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1227_);
                            crate::leanh::lean_dec(v___x_1218_);
                            v___x_1229_ = crate::leanh::lean_box(0);
                            v_isShared_1230_ = v_isSharedCheck_1235_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1222_ == 0 {
                    v___x_1224_ = v___x_1221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1225_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
                    v___x_1224_ = v_reuseFailAlloc_1225_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1224_;
            }
            3 => {
                v___x_1231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1231_, 0, v_a_1227_);
                if v_isShared_1230_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1229_, 0, v___x_1231_);
                    v___x_1233_ = v___x_1229_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1234_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
                    v___x_1233_ = v_reuseFailAlloc_1234_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(
    mut v_x_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1242_: u8 = 0;
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1246_: u8 = 0;
    let mut v_a_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1236_) == 0 {
                    v___x_1237_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0___closed__0;
                    return v___x_1237_;
                } else {
                    v___x_1238_ = l_Lean_Json_getStr_x3f(v_x_1236_);
                    if crate::leanh::lean_obj_tag(v___x_1238_) == 0 {
                        v_a_1239_ = crate::leanh::lean_ctor_get(v___x_1238_, 0);
                        v_isSharedCheck_1246_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1238_)) as u8;
                        if v_isSharedCheck_1246_ == 0 {
                            v___x_1241_ = v___x_1238_;
                            v_isShared_1242_ = v_isSharedCheck_1246_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1239_);
                            crate::leanh::lean_dec(v___x_1238_);
                            v___x_1241_ = crate::leanh::lean_box(0);
                            v_isShared_1242_ = v_isSharedCheck_1246_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1247_ = crate::leanh::lean_ctor_get(v___x_1238_, 0);
                        v_isSharedCheck_1255_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1238_)) as u8;
                        if v_isSharedCheck_1255_ == 0 {
                            v___x_1249_ = v___x_1238_;
                            v_isShared_1250_ = v_isSharedCheck_1255_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1247_);
                            crate::leanh::lean_dec(v___x_1238_);
                            v___x_1249_ = crate::leanh::lean_box(0);
                            v_isShared_1250_ = v_isSharedCheck_1255_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1242_ == 0 {
                    v___x_1244_ = v___x_1241_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1245_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
                    v___x_1244_ = v_reuseFailAlloc_1245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1244_;
            }
            3 => {
                v___x_1251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1251_, 0, v_a_1247_);
                if v_isShared_1250_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1249_, 0, v___x_1251_);
                    v___x_1253_ = v___x_1249_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
                    v___x_1253_ = v_reuseFailAlloc_1254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_RegistrySrc_fromJson_x3f(
    mut v_val_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1279_: u8 = 0;
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v_val_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_isSharedCheck_1356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1274_ = l_Lean_Json_getObj_x3f(v_val_1268_);
                if crate::leanh::lean_obj_tag(v___x_1274_) == 0 {
                    v_a_1275_ = crate::leanh::lean_ctor_get(v___x_1274_, 0);
                    crate::leanh::lean_inc(v_a_1275_);
                    crate::leanh::lean_dec_ref_known(v___x_1274_, 1);
                    v_a_1270_ = v_a_1275_;
                    state = 1;
                    continue;
                } else {
                    v_a_1276_ = crate::leanh::lean_ctor_get(v___x_1274_, 0);
                    v_isSharedCheck_1356_ = (!crate::leanh::lean_is_exclusive(v___x_1274_)) as u8;
                    if v_isSharedCheck_1356_ == 0 {
                        v___x_1278_ = v___x_1274_;
                        v_isShared_1279_ = v_isSharedCheck_1356_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1276_);
                        crate::leanh::lean_dec(v___x_1274_);
                        v___x_1278_ = crate::leanh::lean_box(0);
                        v_isShared_1279_ = v_isSharedCheck_1356_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1271_ = l_Lake_RegistrySrc_fromJson_x3f___closed__0;
                v___x_1272_ = lean_string_append(v___x_1271_, v_a_1270_);
                crate::leanh::lean_dec_ref(v_a_1270_);
                v___x_1273_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1273_, 0, v___x_1272_);
                return v___x_1273_;
            }
            2 => {
                v___x_1285_ = l_Lake_RegistrySrc_fromJson_x3f___closed__1;
                v___x_1286_ = l_Lake_JsonObject_getJson_x3f(v_a_1276_, v___x_1285_);
                if crate::leanh::lean_obj_tag(v___x_1286_) == 0 {
                    state = 3;
                    continue;
                } else {
                    v_val_1287_ = crate::leanh::lean_ctor_get(v___x_1286_, 0);
                    crate::leanh::lean_inc(v_val_1287_);
                    crate::leanh::lean_dec_ref_known(v___x_1286_, 1);
                    v___x_1288_ =
                        l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(
                            v_val_1287_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1288_) == 0 {
                        crate::leanh::lean_del_object(v___x_1278_);
                        crate::leanh::lean_dec(v_a_1276_);
                        v_a_1289_ = crate::leanh::lean_ctor_get(v___x_1288_, 0);
                        crate::leanh::lean_inc(v_a_1289_);
                        crate::leanh::lean_dec_ref_known(v___x_1288_, 1);
                        v___x_1290_ = l_Lake_RegistrySrc_fromJson_x3f___closed__2;
                        v___x_1291_ = lean_string_append(v___x_1290_, v_a_1289_);
                        crate::leanh::lean_dec(v_a_1289_);
                        v_a_1270_ = v___x_1291_;
                        state = 1;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1288_) == 0 {
                            crate::leanh::lean_del_object(v___x_1278_);
                            crate::leanh::lean_dec(v_a_1276_);
                            v_a_1292_ = crate::leanh::lean_ctor_get(v___x_1288_, 0);
                            crate::leanh::lean_inc(v_a_1292_);
                            crate::leanh::lean_dec_ref_known(v___x_1288_, 1);
                            v_a_1270_ = v_a_1292_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1293_ = crate::leanh::lean_ctor_get(v___x_1288_, 0);
                            v_isSharedCheck_1355_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1288_)) as u8;
                            if v_isSharedCheck_1355_ == 0 {
                                v___x_1295_ = v___x_1288_;
                                v_isShared_1296_ = v_isSharedCheck_1355_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1293_);
                                crate::leanh::lean_dec(v___x_1288_);
                                v___x_1295_ = crate::leanh::lean_box(0);
                                v_isShared_1296_ = v_isSharedCheck_1355_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_1281_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1281_, 0, v_a_1276_);
                if v_isShared_1279_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1278_, 0, v___x_1281_);
                    v___x_1283_ = v___x_1278_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
                    v___x_1283_ = v_reuseFailAlloc_1284_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1283_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_1293_) == 1 {
                    crate::leanh::lean_del_object(v___x_1278_);
                    v_val_1297_ = crate::leanh::lean_ctor_get(v_a_1293_, 0);
                    crate::leanh::lean_inc(v_val_1297_);
                    crate::leanh::lean_dec_ref_known(v_a_1293_, 1);
                    v___x_1331_ = l_Lake_RegistrySrc_fromJson_x3f___closed__7;
                    v___x_1332_ = l_Lake_JsonObject_getJson_x3f(v_a_1276_, v___x_1331_);
                    if crate::leanh::lean_obj_tag(v___x_1332_) == 0 {
                        v___x_1333_ = crate::leanh::lean_box(0);
                        v_a_1320_ = v___x_1333_;
                        state = 9;
                        continue;
                    } else {
                        v_val_1334_ = crate::leanh::lean_ctor_get(v___x_1332_, 0);
                        crate::leanh::lean_inc(v_val_1334_);
                        crate::leanh::lean_dec_ref_known(v___x_1332_, 1);
                        v___x_1335_ =
                            l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(
                                v_val_1334_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_1335_) == 0 {
                            crate::leanh::lean_dec(v_val_1297_);
                            crate::leanh::lean_del_object(v___x_1295_);
                            crate::leanh::lean_dec(v_a_1276_);
                            v_a_1336_ = crate::leanh::lean_ctor_get(v___x_1335_, 0);
                            crate::leanh::lean_inc(v_a_1336_);
                            crate::leanh::lean_dec_ref_known(v___x_1335_, 1);
                            v___x_1337_ = l_Lake_RegistrySrc_fromJson_x3f___closed__8;
                            v___x_1338_ = lean_string_append(v___x_1337_, v_a_1336_);
                            crate::leanh::lean_dec(v_a_1336_);
                            v_a_1270_ = v___x_1338_;
                            state = 1;
                            continue;
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_1335_) == 0 {
                                crate::leanh::lean_dec(v_val_1297_);
                                crate::leanh::lean_del_object(v___x_1295_);
                                crate::leanh::lean_dec(v_a_1276_);
                                v_a_1339_ = crate::leanh::lean_ctor_get(v___x_1335_, 0);
                                crate::leanh::lean_inc(v_a_1339_);
                                crate::leanh::lean_dec_ref_known(v___x_1335_, 1);
                                v_a_1270_ = v_a_1339_;
                                state = 1;
                                continue;
                            } else {
                                v_a_1340_ = crate::leanh::lean_ctor_get(v___x_1335_, 0);
                                crate::leanh::lean_inc(v_a_1340_);
                                crate::leanh::lean_dec_ref_known(v___x_1335_, 1);
                                if crate::leanh::lean_obj_tag(v_a_1340_) == 0 {
                                    v_a_1320_ = v_a_1340_;
                                    state = 9;
                                    continue;
                                } else {
                                    v_val_1341_ = crate::leanh::lean_ctor_get(v_a_1340_, 0);
                                    crate::leanh::lean_inc(v_val_1341_);
                                    crate::leanh::lean_dec_ref_known(v_a_1340_, 1);
                                    v___x_1342_ = l_Lake_RegistrySrc_fromJson_x3f___closed__9;
                                    v___x_1343_ = lean_string_dec_eq(v_val_1341_, v___x_1342_);
                                    crate::leanh::lean_dec(v_val_1341_);
                                    if v___x_1343_ == 0 {
                                        v___x_1344_ = crate::leanh::lean_box(0);
                                        v_a_1320_ = v___x_1344_;
                                        state = 9;
                                        continue;
                                    } else {
                                        v___x_1345_ = l_Lake_RegistrySrc_fromJson_x3f___closed__10;
                                        v___x_1346_ =
                                            l_Lake_JsonObject_getJson_x3f(v_a_1276_, v___x_1345_);
                                        if crate::leanh::lean_obj_tag(v___x_1346_) == 0 {
                                            v___x_1347_ = crate::leanh::lean_box(0);
                                            v_a_1320_ = v___x_1347_;
                                            state = 9;
                                            continue;
                                        } else {
                                            v_val_1348_ =
                                                crate::leanh::lean_ctor_get(v___x_1346_, 0);
                                            crate::leanh::lean_inc(v_val_1348_);
                                            crate::leanh::lean_dec_ref_known(v___x_1346_, 1);
                                            v___x_1349_ = l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(v_val_1348_);
                                            if crate::leanh::lean_obj_tag(v___x_1349_) == 0 {
                                                crate::leanh::lean_dec(v_val_1297_);
                                                crate::leanh::lean_del_object(v___x_1295_);
                                                crate::leanh::lean_dec(v_a_1276_);
                                                v_a_1350_ =
                                                    crate::leanh::lean_ctor_get(v___x_1349_, 0);
                                                crate::leanh::lean_inc(v_a_1350_);
                                                crate::leanh::lean_dec_ref_known(v___x_1349_, 1);
                                                v___x_1351_ =
                                                    l_Lake_RegistrySrc_fromJson_x3f___closed__11;
                                                v___x_1352_ =
                                                    lean_string_append(v___x_1351_, v_a_1350_);
                                                crate::leanh::lean_dec(v_a_1350_);
                                                v_a_1270_ = v___x_1352_;
                                                state = 1;
                                                continue;
                                            } else {
                                                if crate::leanh::lean_obj_tag(v___x_1349_) == 0 {
                                                    crate::leanh::lean_dec(v_val_1297_);
                                                    crate::leanh::lean_del_object(v___x_1295_);
                                                    crate::leanh::lean_dec(v_a_1276_);
                                                    v_a_1353_ =
                                                        crate::leanh::lean_ctor_get(v___x_1349_, 0);
                                                    crate::leanh::lean_inc(v_a_1353_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1349_,
                                                        1,
                                                    );
                                                    v_a_1270_ = v_a_1353_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v_a_1354_ =
                                                        crate::leanh::lean_ctor_get(v___x_1349_, 0);
                                                    crate::leanh::lean_inc(v_a_1354_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1349_,
                                                        1,
                                                    );
                                                    v_a_1320_ = v_a_1354_;
                                                    state = 9;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1295_);
                    crate::leanh::lean_dec(v_a_1293_);
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_1302_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1302_, 0, v_a_1276_);
                crate::leanh::lean_ctor_set(v___x_1302_, 1, v_val_1297_);
                crate::leanh::lean_ctor_set(v___x_1302_, 2, v___y_1299_);
                crate::leanh::lean_ctor_set(v___x_1302_, 3, v___y_1300_);
                crate::leanh::lean_ctor_set(v___x_1302_, 4, v_a_1301_);
                if v_isShared_1296_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1295_, 0, v___x_1302_);
                    v___x_1304_ = v___x_1295_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
                    v___x_1304_ = v_reuseFailAlloc_1305_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1304_;
            }
            8 => {
                v___x_1309_ = l_Lake_RegistrySrc_fromJson_x3f___closed__3;
                v___x_1310_ = l_Lake_JsonObject_getJson_x3f(v_a_1276_, v___x_1309_);
                if crate::leanh::lean_obj_tag(v___x_1310_) == 0 {
                    v___x_1311_ = crate::leanh::lean_box(0);
                    v___y_1299_ = v___y_1307_;
                    v___y_1300_ = v_a_1308_;
                    v_a_1301_ = v___x_1311_;
                    state = 6;
                    continue;
                } else {
                    v_val_1312_ = crate::leanh::lean_ctor_get(v___x_1310_, 0);
                    crate::leanh::lean_inc(v_val_1312_);
                    crate::leanh::lean_dec_ref_known(v___x_1310_, 1);
                    v___x_1313_ =
                        l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__1(
                            v_val_1312_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1313_) == 0 {
                        crate::leanh::lean_dec(v_a_1308_);
                        crate::leanh::lean_dec(v___y_1307_);
                        crate::leanh::lean_dec(v_val_1297_);
                        crate::leanh::lean_del_object(v___x_1295_);
                        crate::leanh::lean_dec(v_a_1276_);
                        v_a_1314_ = crate::leanh::lean_ctor_get(v___x_1313_, 0);
                        crate::leanh::lean_inc(v_a_1314_);
                        crate::leanh::lean_dec_ref_known(v___x_1313_, 1);
                        v___x_1315_ = l_Lake_RegistrySrc_fromJson_x3f___closed__4;
                        v___x_1316_ = lean_string_append(v___x_1315_, v_a_1314_);
                        crate::leanh::lean_dec(v_a_1314_);
                        v_a_1270_ = v___x_1316_;
                        state = 1;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1313_) == 0 {
                            crate::leanh::lean_dec(v_a_1308_);
                            crate::leanh::lean_dec(v___y_1307_);
                            crate::leanh::lean_dec(v_val_1297_);
                            crate::leanh::lean_del_object(v___x_1295_);
                            crate::leanh::lean_dec(v_a_1276_);
                            v_a_1317_ = crate::leanh::lean_ctor_get(v___x_1313_, 0);
                            crate::leanh::lean_inc(v_a_1317_);
                            crate::leanh::lean_dec_ref_known(v___x_1313_, 1);
                            v_a_1270_ = v_a_1317_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1318_ = crate::leanh::lean_ctor_get(v___x_1313_, 0);
                            crate::leanh::lean_inc(v_a_1318_);
                            crate::leanh::lean_dec_ref_known(v___x_1313_, 1);
                            v___y_1299_ = v___y_1307_;
                            v___y_1300_ = v_a_1308_;
                            v_a_1301_ = v_a_1318_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v___x_1321_ = l_Lake_RegistrySrc_fromJson_x3f___closed__5;
                v___x_1322_ = l_Lake_JsonObject_getJson_x3f(v_a_1276_, v___x_1321_);
                if crate::leanh::lean_obj_tag(v___x_1322_) == 0 {
                    v___x_1323_ = crate::leanh::lean_box(0);
                    v___y_1307_ = v_a_1320_;
                    v_a_1308_ = v___x_1323_;
                    state = 8;
                    continue;
                } else {
                    v_val_1324_ = crate::leanh::lean_ctor_get(v___x_1322_, 0);
                    crate::leanh::lean_inc(v_val_1324_);
                    crate::leanh::lean_dec_ref_known(v___x_1322_, 1);
                    v___x_1325_ =
                        l_Option_fromJson_x3f___at___00Lake_RegistrySrc_fromJson_x3f_spec__0(
                            v_val_1324_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1325_) == 0 {
                        crate::leanh::lean_dec(v_a_1320_);
                        crate::leanh::lean_dec(v_val_1297_);
                        crate::leanh::lean_del_object(v___x_1295_);
                        crate::leanh::lean_dec(v_a_1276_);
                        v_a_1326_ = crate::leanh::lean_ctor_get(v___x_1325_, 0);
                        crate::leanh::lean_inc(v_a_1326_);
                        crate::leanh::lean_dec_ref_known(v___x_1325_, 1);
                        v___x_1327_ = l_Lake_RegistrySrc_fromJson_x3f___closed__6;
                        v___x_1328_ = lean_string_append(v___x_1327_, v_a_1326_);
                        crate::leanh::lean_dec(v_a_1326_);
                        v_a_1270_ = v___x_1328_;
                        state = 1;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1325_) == 0 {
                            crate::leanh::lean_dec(v_a_1320_);
                            crate::leanh::lean_dec(v_val_1297_);
                            crate::leanh::lean_del_object(v___x_1295_);
                            crate::leanh::lean_dec(v_a_1276_);
                            v_a_1329_ = crate::leanh::lean_ctor_get(v___x_1325_, 0);
                            crate::leanh::lean_inc(v_a_1329_);
                            crate::leanh::lean_dec_ref_known(v___x_1325_, 1);
                            v_a_1270_ = v_a_1329_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1330_ = crate::leanh::lean_ctor_get(v___x_1325_, 0);
                            crate::leanh::lean_inc(v_a_1330_);
                            crate::leanh::lean_dec_ref_known(v___x_1325_, 1);
                            v___y_1307_ = v_a_1320_;
                            v_a_1308_ = v_a_1330_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(
    mut v_as_1370_: *mut crate::leanh::LeanObject,
    mut v_sz_1371_: usize,
    mut v_i_1372_: usize,
    mut v_b_1373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: usize = 0;
    let mut v___x_1380_: usize = 0;
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1374_ = lean_usize_dec_lt(v_i_1372_, v_sz_1371_);
                if v___x_1374_ == 0 {
                    crate::leanh::lean_inc_ref(v_b_1373_);
                    return v_b_1373_;
                } else {
                    v___x_1375_ = crate::leanh::lean_box(0);
                    v_a_1376_ = lean_array_uget_borrowed(v_as_1370_, v_i_1372_);
                    v___x_1377_ = l_Lake_RegistrySrc_isGit(v_a_1376_);
                    if v___x_1377_ == 0 {
                        v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0;
                        v___x_1379_ = 1usize;
                        v___x_1380_ = lean_usize_add(v_i_1372_, v___x_1379_);
                        v_i_1372_ = v___x_1380_;
                        v_b_1373_ = v___x_1378_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1376_);
                        v___x_1382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1382_, 0, v_a_1376_);
                        v___x_1383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1383_, 0, v___x_1382_);
                        v___x_1384_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1384_, 0, v___x_1383_);
                        crate::leanh::lean_ctor_set(v___x_1384_, 1, v___x_1375_);
                        return v___x_1384_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___boxed(
    mut v_as_1385_: *mut crate::leanh::LeanObject,
    mut v_sz_1386_: *mut crate::leanh::LeanObject,
    mut v_i_1387_: *mut crate::leanh::LeanObject,
    mut v_b_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1389_: usize = 0;
    let mut v_i_boxed_1390_: usize = 0;
    let mut v_res_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1389_ = crate::leanh::lean_unbox_usize(v_sz_1386_);
    crate::leanh::lean_dec(v_sz_1386_);
    v_i_boxed_1390_ = crate::leanh::lean_unbox_usize(v_i_1387_);
    crate::leanh::lean_dec(v_i_1387_);
    v_res_1391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_as_1385_, v_sz_boxed_1389_, v_i_boxed_1390_, v_b_1388_);
    crate::leanh::lean_dec_ref(v_b_1388_);
    crate::leanh::lean_dec_ref(v_as_1385_);
    return v_res_1391_;
}
pub unsafe fn l_Lake_RegistryPkg_gitSrc_x3f(
    mut v_pkg_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sources_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1396_: usize = 0;
    let mut v___x_1397_: usize = 0;
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sources_1393_ = crate::leanh::lean_ctor_get(v_pkg_1392_, 2);
    v___x_1394_ = crate::leanh::lean_box(0);
    v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0___closed__0;
    v_sz_1396_ = lean_array_size(v_sources_1393_);
    v___x_1397_ = 0usize;
    v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_RegistryPkg_gitSrc_x3f_spec__0(v_sources_1393_, v_sz_1396_, v___x_1397_, v___x_1395_);
    v_fst_1399_ = crate::leanh::lean_ctor_get(v___x_1398_, 0);
    crate::leanh::lean_inc(v_fst_1399_);
    crate::leanh::lean_dec_ref(v___x_1398_);
    if crate::leanh::lean_obj_tag(v_fst_1399_) == 0 {
        return v___x_1394_;
    } else {
        let mut v_val_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1400_ = crate::leanh::lean_ctor_get(v_fst_1399_, 0);
        crate::leanh::lean_inc(v_val_1400_);
        crate::leanh::lean_dec_ref_known(v_fst_1399_, 1);
        return v_val_1400_;
    }
}
pub unsafe fn l_Lake_RegistryPkg_gitSrc_x3f___boxed(
    mut v_pkg_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1402_ = l_Lake_RegistryPkg_gitSrc_x3f(v_pkg_1401_);
    crate::leanh::lean_dec_ref(v_pkg_1401_);
    return v_res_1402_;
}
pub unsafe fn l_Lake_RegistryPkg_toJson(
    mut v_src_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_data_1404_ = crate::leanh::lean_ctor_get(v_src_1403_, 3);
    crate::leanh::lean_inc(v_data_1404_);
    return v_data_1404_;
}
pub unsafe fn l_Lake_RegistryPkg_toJson___boxed(
    mut v_src_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1406_ = l_Lake_RegistryPkg_toJson(v_src_1405_);
    crate::leanh::lean_dec_ref(v_src_1405_);
    return v_res_1406_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(
    mut v_sz_1409_: usize,
    mut v_i_1410_: usize,
    mut v_bs_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1412_: u8 = 0;
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: usize = 0;
    let mut v___x_1418_: usize = 0;
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1412_ = lean_usize_dec_lt(v_i_1410_, v_sz_1409_);
                if v___x_1412_ == 0 {
                    v___x_1413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1413_, 0, v_bs_1411_);
                    return v___x_1413_;
                } else {
                    v_v_1414_ = lean_array_uget(v_bs_1411_, v_i_1410_);
                    v___x_1415_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1416_ = lean_array_uset(v_bs_1411_, v_i_1410_, v___x_1415_);
                    v___x_1417_ = 1usize;
                    v___x_1418_ = lean_usize_add(v_i_1410_, v___x_1417_);
                    v___x_1419_ = lean_array_uset(v_bs_x27_1416_, v_i_1410_, v_v_1414_);
                    v_i_1410_ = v___x_1418_;
                    v_bs_1411_ = v___x_1419_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2___boxed(
    mut v_sz_1421_: *mut crate::leanh::LeanObject,
    mut v_i_1422_: *mut crate::leanh::LeanObject,
    mut v_bs_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1424_: usize = 0;
    let mut v_i_boxed_1425_: usize = 0;
    let mut v_res_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1424_ = crate::leanh::lean_unbox_usize(v_sz_1421_);
    crate::leanh::lean_dec(v_sz_1421_);
    v_i_boxed_1425_ = crate::leanh::lean_unbox_usize(v_i_1422_);
    crate::leanh::lean_dec(v_i_1422_);
    v_res_1426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_boxed_1424_, v_i_boxed_1425_, v_bs_1423_);
    return v_res_1426_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(
    mut v_x_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1429_) == 4 {
        let mut v_elems_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1431_: usize = 0;
        let mut v___x_1432_: usize = 0;
        let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_1430_ = crate::leanh::lean_ctor_get(v_x_1429_, 0);
        crate::leanh::lean_inc_ref(v_elems_1430_);
        crate::leanh::lean_dec_ref_known(v_x_1429_, 1);
        v_sz_1431_ = lean_array_size(v_elems_1430_);
        v___x_1432_ = 0usize;
        v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1_spec__2(v_sz_1431_, v___x_1432_, v_elems_1430_);
        return v___x_1433_;
    } else {
        let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1434_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0;
        v___x_1435_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_1436_ = l_Lean_Json_pretty(v_x_1429_, v___x_1435_);
        v___x_1437_ = lean_string_append(v___x_1434_, v___x_1436_);
        crate::leanh::lean_dec_ref(v___x_1436_);
        v___x_1438_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1;
        v___x_1439_ = lean_string_append(v___x_1437_, v___x_1438_);
        v___x_1440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1440_, 0, v___x_1439_);
        return v___x_1440_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(
    mut v_x_1443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_a_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1457_: u8 = 0;
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1443_) == 0 {
                    v___x_1444_ = l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1___closed__0;
                    return v___x_1444_;
                } else {
                    v___x_1445_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1(v_x_1443_);
                    if crate::leanh::lean_obj_tag(v___x_1445_) == 0 {
                        v_a_1446_ = crate::leanh::lean_ctor_get(v___x_1445_, 0);
                        v_isSharedCheck_1453_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1445_)) as u8;
                        if v_isSharedCheck_1453_ == 0 {
                            v___x_1448_ = v___x_1445_;
                            v_isShared_1449_ = v_isSharedCheck_1453_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1446_);
                            crate::leanh::lean_dec(v___x_1445_);
                            v___x_1448_ = crate::leanh::lean_box(0);
                            v_isShared_1449_ = v_isSharedCheck_1453_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1454_ = crate::leanh::lean_ctor_get(v___x_1445_, 0);
                        v_isSharedCheck_1462_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1445_)) as u8;
                        if v_isSharedCheck_1462_ == 0 {
                            v___x_1456_ = v___x_1445_;
                            v_isShared_1457_ = v_isSharedCheck_1462_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1454_);
                            crate::leanh::lean_dec(v___x_1445_);
                            v___x_1456_ = crate::leanh::lean_box(0);
                            v_isShared_1457_ = v_isSharedCheck_1462_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1449_ == 0 {
                    v___x_1451_ = v___x_1448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
                    v___x_1451_ = v_reuseFailAlloc_1452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1451_;
            }
            3 => {
                v___x_1458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1458_, 0, v_a_1454_);
                if v_isShared_1457_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1456_, 0, v___x_1458_);
                    v___x_1460_ = v___x_1456_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1461_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
                    v___x_1460_ = v_reuseFailAlloc_1461_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(
    mut v_sz_1463_: usize,
    mut v_i_1464_: usize,
    mut v_bs_1465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1466_: u8 = 0;
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut v_a_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: usize = 0;
    let mut v___x_1482_: usize = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1466_ = lean_usize_dec_lt(v_i_1464_, v_sz_1463_);
                if v___x_1466_ == 0 {
                    v___x_1467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v_bs_1465_);
                    return v___x_1467_;
                } else {
                    v_v_1468_ = lean_array_uget_borrowed(v_bs_1465_, v_i_1464_);
                    crate::leanh::lean_inc(v_v_1468_);
                    v___x_1469_ = l_Lake_RegistrySrc_fromJson_x3f(v_v_1468_);
                    if crate::leanh::lean_obj_tag(v___x_1469_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_1465_);
                        v_a_1470_ = crate::leanh::lean_ctor_get(v___x_1469_, 0);
                        v_isSharedCheck_1477_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1469_)) as u8;
                        if v_isSharedCheck_1477_ == 0 {
                            v___x_1472_ = v___x_1469_;
                            v_isShared_1473_ = v_isSharedCheck_1477_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1470_);
                            crate::leanh::lean_dec(v___x_1469_);
                            v___x_1472_ = crate::leanh::lean_box(0);
                            v_isShared_1473_ = v_isSharedCheck_1477_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1478_ = crate::leanh::lean_ctor_get(v___x_1469_, 0);
                        crate::leanh::lean_inc(v_a_1478_);
                        crate::leanh::lean_dec_ref_known(v___x_1469_, 1);
                        v___x_1479_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1480_ = lean_array_uset(v_bs_1465_, v_i_1464_, v___x_1479_);
                        v___x_1481_ = 1usize;
                        v___x_1482_ = lean_usize_add(v_i_1464_, v___x_1481_);
                        v___x_1483_ = lean_array_uset(v_bs_x27_1480_, v_i_1464_, v_a_1478_);
                        v_i_1464_ = v___x_1482_;
                        v_bs_1465_ = v___x_1483_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1473_ == 0 {
                    v___x_1475_ = v___x_1472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
                    v___x_1475_ = v_reuseFailAlloc_1476_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0___boxed(
    mut v_sz_1485_: *mut crate::leanh::LeanObject,
    mut v_i_1486_: *mut crate::leanh::LeanObject,
    mut v_bs_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1488_: usize = 0;
    let mut v_i_boxed_1489_: usize = 0;
    let mut v_res_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1488_ = crate::leanh::lean_unbox_usize(v_sz_1485_);
    crate::leanh::lean_dec(v_sz_1485_);
    v_i_boxed_1489_ = crate::leanh::lean_unbox_usize(v_i_1486_);
    crate::leanh::lean_dec(v_i_1486_);
    v_res_1490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_boxed_1488_, v_i_boxed_1489_, v_bs_1487_);
    return v_res_1490_;
}
pub unsafe fn l_Lake_RegistryPkg_fromJson_x3f(
    mut v_val_1502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v_a_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1536_: usize = 0;
    let mut v___x_1537_: usize = 0;
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1543_: u8 = 0;
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1551_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1564_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1508_ = l_Lean_Json_getObj_x3f(v_val_1502_);
                if crate::leanh::lean_obj_tag(v___x_1508_) == 0 {
                    v_a_1509_ = crate::leanh::lean_ctor_get(v___x_1508_, 0);
                    crate::leanh::lean_inc(v_a_1509_);
                    crate::leanh::lean_dec_ref_known(v___x_1508_, 1);
                    v_a_1504_ = v_a_1509_;
                    state = 1;
                    continue;
                } else {
                    v_a_1510_ = crate::leanh::lean_ctor_get(v___x_1508_, 0);
                    crate::leanh::lean_inc(v_a_1510_);
                    crate::leanh::lean_dec_ref_known(v___x_1508_, 1);
                    v___x_1511_ = l_Lake_RegistryPkg_fromJson_x3f___closed__1;
                    v___x_1512_ = l_Lake_JsonObject_getJson_x3f(v_a_1510_, v___x_1511_);
                    if crate::leanh::lean_obj_tag(v___x_1512_) == 0 {
                        crate::leanh::lean_dec(v_a_1510_);
                        v___x_1513_ = l_Lake_RegistryPkg_fromJson_x3f___closed__2;
                        v_a_1504_ = v___x_1513_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1514_ = crate::leanh::lean_ctor_get(v___x_1512_, 0);
                        crate::leanh::lean_inc(v_val_1514_);
                        crate::leanh::lean_dec_ref_known(v___x_1512_, 1);
                        v___x_1515_ = l_Lean_Json_getStr_x3f(v_val_1514_);
                        if crate::leanh::lean_obj_tag(v___x_1515_) == 0 {
                            crate::leanh::lean_dec(v_a_1510_);
                            v_a_1516_ = crate::leanh::lean_ctor_get(v___x_1515_, 0);
                            crate::leanh::lean_inc(v_a_1516_);
                            crate::leanh::lean_dec_ref_known(v___x_1515_, 1);
                            v___x_1517_ = l_Lake_RegistryPkg_fromJson_x3f___closed__3;
                            v___x_1518_ = lean_string_append(v___x_1517_, v_a_1516_);
                            crate::leanh::lean_dec(v_a_1516_);
                            v_a_1504_ = v___x_1518_;
                            state = 1;
                            continue;
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_1515_) == 0 {
                                crate::leanh::lean_dec(v_a_1510_);
                                v_a_1519_ = crate::leanh::lean_ctor_get(v___x_1515_, 0);
                                crate::leanh::lean_inc(v_a_1519_);
                                crate::leanh::lean_dec_ref_known(v___x_1515_, 1);
                                v_a_1504_ = v_a_1519_;
                                state = 1;
                                continue;
                            } else {
                                v_a_1520_ = crate::leanh::lean_ctor_get(v___x_1515_, 0);
                                crate::leanh::lean_inc(v_a_1520_);
                                crate::leanh::lean_dec_ref_known(v___x_1515_, 1);
                                v___x_1521_ = l_Lake_RegistryPkg_fromJson_x3f___closed__4;
                                v___x_1522_ = l_Lake_JsonObject_getJson_x3f(v_a_1510_, v___x_1521_);
                                if crate::leanh::lean_obj_tag(v___x_1522_) == 0 {
                                    crate::leanh::lean_dec(v_a_1520_);
                                    crate::leanh::lean_dec(v_a_1510_);
                                    v___x_1523_ = l_Lake_RegistryPkg_fromJson_x3f___closed__5;
                                    v_a_1504_ = v___x_1523_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_1524_ = crate::leanh::lean_ctor_get(v___x_1522_, 0);
                                    crate::leanh::lean_inc(v_val_1524_);
                                    crate::leanh::lean_dec_ref_known(v___x_1522_, 1);
                                    v___x_1525_ = l_Lean_Json_getStr_x3f(v_val_1524_);
                                    if crate::leanh::lean_obj_tag(v___x_1525_) == 0 {
                                        crate::leanh::lean_dec(v_a_1520_);
                                        crate::leanh::lean_dec(v_a_1510_);
                                        v_a_1526_ = crate::leanh::lean_ctor_get(v___x_1525_, 0);
                                        crate::leanh::lean_inc(v_a_1526_);
                                        crate::leanh::lean_dec_ref_known(v___x_1525_, 1);
                                        v___x_1527_ = l_Lake_RegistryPkg_fromJson_x3f___closed__6;
                                        v___x_1528_ = lean_string_append(v___x_1527_, v_a_1526_);
                                        crate::leanh::lean_dec(v_a_1526_);
                                        v_a_1504_ = v___x_1528_;
                                        state = 1;
                                        continue;
                                    } else {
                                        if crate::leanh::lean_obj_tag(v___x_1525_) == 0 {
                                            crate::leanh::lean_dec(v_a_1520_);
                                            crate::leanh::lean_dec(v_a_1510_);
                                            v_a_1529_ = crate::leanh::lean_ctor_get(v___x_1525_, 0);
                                            crate::leanh::lean_inc(v_a_1529_);
                                            crate::leanh::lean_dec_ref_known(v___x_1525_, 1);
                                            v_a_1504_ = v_a_1529_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_1530_ = crate::leanh::lean_ctor_get(v___x_1525_, 0);
                                            v_isSharedCheck_1564_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1525_))
                                                    as u8;
                                            if v_isSharedCheck_1564_ == 0 {
                                                v___x_1532_ = v___x_1525_;
                                                v_isShared_1533_ = v_isSharedCheck_1564_;
                                                state = 2;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1530_);
                                                crate::leanh::lean_dec(v___x_1525_);
                                                v___x_1532_ = crate::leanh::lean_box(0);
                                                v_isShared_1533_ = v_isSharedCheck_1564_;
                                                state = 2;
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
            1 => {
                v___x_1505_ = l_Lake_RegistryPkg_fromJson_x3f___closed__0;
                v___x_1506_ = lean_string_append(v___x_1505_, v_a_1504_);
                crate::leanh::lean_dec_ref(v_a_1504_);
                v___x_1507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1506_);
                return v___x_1507_;
            }
            2 => {
                v___x_1554_ = l_Lake_RegistryPkg_fromJson_x3f___closed__8;
                v___x_1555_ = l_Lake_JsonObject_getJson_x3f(v_a_1510_, v___x_1554_);
                if crate::leanh::lean_obj_tag(v___x_1555_) == 0 {
                    state = 7;
                    continue;
                } else {
                    v_val_1556_ = crate::leanh::lean_ctor_get(v___x_1555_, 0);
                    crate::leanh::lean_inc(v_val_1556_);
                    crate::leanh::lean_dec_ref_known(v___x_1555_, 1);
                    v___x_1557_ =
                        l_Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1(
                            v_val_1556_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1557_) == 0 {
                        crate::leanh::lean_del_object(v___x_1532_);
                        crate::leanh::lean_dec(v_a_1530_);
                        crate::leanh::lean_dec(v_a_1520_);
                        crate::leanh::lean_dec(v_a_1510_);
                        v_a_1558_ = crate::leanh::lean_ctor_get(v___x_1557_, 0);
                        crate::leanh::lean_inc(v_a_1558_);
                        crate::leanh::lean_dec_ref_known(v___x_1557_, 1);
                        v___x_1559_ = l_Lake_RegistryPkg_fromJson_x3f___closed__9;
                        v___x_1560_ = lean_string_append(v___x_1559_, v_a_1558_);
                        crate::leanh::lean_dec(v_a_1558_);
                        v_a_1504_ = v___x_1560_;
                        state = 1;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1557_) == 0 {
                            crate::leanh::lean_del_object(v___x_1532_);
                            crate::leanh::lean_dec(v_a_1530_);
                            crate::leanh::lean_dec(v_a_1520_);
                            crate::leanh::lean_dec(v_a_1510_);
                            v_a_1561_ = crate::leanh::lean_ctor_get(v___x_1557_, 0);
                            crate::leanh::lean_inc(v_a_1561_);
                            crate::leanh::lean_dec_ref_known(v___x_1557_, 1);
                            v_a_1504_ = v_a_1561_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1562_ = crate::leanh::lean_ctor_get(v___x_1557_, 0);
                            crate::leanh::lean_inc(v_a_1562_);
                            crate::leanh::lean_dec_ref_known(v___x_1557_, 1);
                            if crate::leanh::lean_obj_tag(v_a_1562_) == 0 {
                                state = 7;
                                continue;
                            } else {
                                v_val_1563_ = crate::leanh::lean_ctor_get(v_a_1562_, 0);
                                crate::leanh::lean_inc(v_val_1563_);
                                crate::leanh::lean_dec_ref_known(v_a_1562_, 1);
                                v_a_1535_ = v_val_1563_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v_sz_1536_ = lean_array_size(v_a_1535_);
                v___x_1537_ = 0usize;
                v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_RegistryPkg_fromJson_x3f_spec__0(v_sz_1536_, v___x_1537_, v_a_1535_);
                if crate::leanh::lean_obj_tag(v___x_1538_) == 0 {
                    crate::leanh::lean_del_object(v___x_1532_);
                    crate::leanh::lean_dec(v_a_1530_);
                    crate::leanh::lean_dec(v_a_1520_);
                    crate::leanh::lean_dec(v_a_1510_);
                    v_a_1539_ = crate::leanh::lean_ctor_get(v___x_1538_, 0);
                    crate::leanh::lean_inc(v_a_1539_);
                    crate::leanh::lean_dec_ref_known(v___x_1538_, 1);
                    v_a_1504_ = v_a_1539_;
                    state = 1;
                    continue;
                } else {
                    v_a_1540_ = crate::leanh::lean_ctor_get(v___x_1538_, 0);
                    v_isSharedCheck_1551_ = (!crate::leanh::lean_is_exclusive(v___x_1538_)) as u8;
                    if v_isSharedCheck_1551_ == 0 {
                        v___x_1542_ = v___x_1538_;
                        v_isShared_1543_ = v_isSharedCheck_1551_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1540_);
                        crate::leanh::lean_dec(v___x_1538_);
                        v___x_1542_ = crate::leanh::lean_box(0);
                        v_isShared_1543_ = v_isSharedCheck_1551_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1533_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1532_, 5);
                    crate::leanh::lean_ctor_set(v___x_1532_, 0, v_a_1510_);
                    v___x_1545_ = v___x_1532_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1550_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1510_);
                    v___x_1545_ = v_reuseFailAlloc_1550_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1546_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1546_, 0, v_a_1520_);
                crate::leanh::lean_ctor_set(v___x_1546_, 1, v_a_1530_);
                crate::leanh::lean_ctor_set(v___x_1546_, 2, v_a_1540_);
                crate::leanh::lean_ctor_set(v___x_1546_, 3, v___x_1545_);
                if v_isShared_1543_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1542_, 0, v___x_1546_);
                    v___x_1548_ = v___x_1542_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
                    v___x_1548_ = v_reuseFailAlloc_1549_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1548_;
            }
            7 => {
                v___x_1553_ = l_Lake_RegistryPkg_fromJson_x3f___closed__7;
                v_a_1535_ = v___x_1553_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Reservoir_pkgApiUrl(
    mut v_lakeEnv_1569_: *mut crate::leanh::LeanObject,
    mut v_owner_1570_: *mut crate::leanh::LeanObject,
    mut v_pkg_1571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_reservoirApiUrl_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_reservoirApiUrl_1572_ = crate::leanh::lean_ctor_get(v_lakeEnv_1569_, 3);
    crate::leanh::lean_inc_ref(v_reservoirApiUrl_1572_);
    crate::leanh::lean_dec_ref(v_lakeEnv_1569_);
    v___x_1573_ = l_Lake_Reservoir_pkgApiUrl___closed__0;
    v___x_1574_ = lean_string_append(v_reservoirApiUrl_1572_, v___x_1573_);
    v___x_1575_ = l_Lake_instInhabitedRegistrySrc_default___closed__0;
    v___x_1576_ = l_Lake_uriEncode(v_owner_1570_, v___x_1575_);
    v___x_1577_ = lean_string_append(v___x_1574_, v___x_1576_);
    crate::leanh::lean_dec_ref(v___x_1576_);
    v___x_1578_ = l_Lake_Reservoir_pkgApiUrl___closed__1;
    v___x_1579_ = lean_string_append(v___x_1577_, v___x_1578_);
    v___x_1580_ = l_Lake_uriEncode(v_pkg_1571_, v___x_1575_);
    v___x_1581_ = lean_string_append(v___x_1579_, v___x_1580_);
    crate::leanh::lean_dec_ref(v___x_1580_);
    return v___x_1581_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(
    mut v_x_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut v_a_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1598_: u8 = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1584_) == 0 {
                    v___x_1585_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1___closed__0;
                    return v___x_1585_;
                } else {
                    v___x_1586_ = l_Lean_Json_getObj_x3f(v_x_1584_);
                    if crate::leanh::lean_obj_tag(v___x_1586_) == 0 {
                        v_a_1587_ = crate::leanh::lean_ctor_get(v___x_1586_, 0);
                        v_isSharedCheck_1594_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1586_)) as u8;
                        if v_isSharedCheck_1594_ == 0 {
                            v___x_1589_ = v___x_1586_;
                            v_isShared_1590_ = v_isSharedCheck_1594_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1587_);
                            crate::leanh::lean_dec(v___x_1586_);
                            v___x_1589_ = crate::leanh::lean_box(0);
                            v_isShared_1590_ = v_isSharedCheck_1594_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1595_ = crate::leanh::lean_ctor_get(v___x_1586_, 0);
                        v_isSharedCheck_1603_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1586_)) as u8;
                        if v_isSharedCheck_1603_ == 0 {
                            v___x_1597_ = v___x_1586_;
                            v_isShared_1598_ = v_isSharedCheck_1603_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1595_);
                            crate::leanh::lean_dec(v___x_1586_);
                            v___x_1597_ = crate::leanh::lean_box(0);
                            v_isShared_1598_ = v_isSharedCheck_1603_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1590_ == 0 {
                    v___x_1592_ = v___x_1589_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
                    v___x_1592_ = v_reuseFailAlloc_1593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1592_;
            }
            3 => {
                v___x_1599_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1599_, 0, v_a_1595_);
                if v_isShared_1598_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1597_, 0, v___x_1599_);
                    v___x_1601_ = v___x_1597_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
                    v___x_1601_ = v_reuseFailAlloc_1602_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(
    mut v_x_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1606_) == 0 {
        let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1607_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0___closed__0;
        return v___x_1607_;
    } else {
        let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1608_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1608_, 0, v_x_1606_);
        v___x_1609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1609_, 0, v___x_1608_);
        return v___x_1609_;
    }
}
pub unsafe fn l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(
    mut v_val_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1634_: u8 = 0;
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1638_: u8 = 0;
    let mut v_a_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1649_: u8 = 0;
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1655_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1659_: u8 = 0;
    let mut v_a_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1663_: u8 = 0;
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1690_: u8 = 0;
    let mut v_a_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1698_: u8 = 0;
    let mut v_a_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut v_a_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut v_a_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1733_: u8 = 0;
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1739_: u8 = 0;
    let mut v_a_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v_a_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1756_: u8 = 0;
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1765_: u8 = 0;
    let mut v_a_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_val_1623_);
                v___x_1669_ = l_Lean_Json_getObj_x3f(v_val_1623_);
                if crate::leanh::lean_obj_tag(v___x_1669_) == 1 {
                    v_a_1670_ = crate::leanh::lean_ctor_get(v___x_1669_, 0);
                    crate::leanh::lean_inc(v_a_1670_);
                    crate::leanh::lean_dec_ref_known(v___x_1669_, 1);
                    v___x_1677_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1;
                    v___x_1678_ = l_Lake_JsonObject_getJson_x3f(v_a_1670_, v___x_1677_);
                    if crate::leanh::lean_obj_tag(v___x_1678_) == 0 {
                        state = 12;
                        continue;
                    } else {
                        v_val_1679_ = crate::leanh::lean_ctor_get(v___x_1678_, 0);
                        crate::leanh::lean_inc(v_val_1679_);
                        crate::leanh::lean_dec_ref_known(v___x_1678_, 1);
                        v___x_1680_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_1679_);
                        if crate::leanh::lean_obj_tag(v___x_1680_) == 0 {
                            crate::leanh::lean_dec(v_a_1670_);
                            crate::leanh::lean_dec(v_val_1623_);
                            v_a_1681_ = crate::leanh::lean_ctor_get(v___x_1680_, 0);
                            v_isSharedCheck_1690_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1680_)) as u8;
                            if v_isSharedCheck_1690_ == 0 {
                                v___x_1683_ = v___x_1680_;
                                v_isShared_1684_ = v_isSharedCheck_1690_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1681_);
                                crate::leanh::lean_dec(v___x_1680_);
                                v___x_1683_ = crate::leanh::lean_box(0);
                                v_isShared_1684_ = v_isSharedCheck_1690_;
                                state = 13;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_1680_) == 0 {
                                crate::leanh::lean_dec(v_a_1670_);
                                crate::leanh::lean_dec(v_val_1623_);
                                v_a_1691_ = crate::leanh::lean_ctor_get(v___x_1680_, 0);
                                v_isSharedCheck_1698_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1680_)) as u8;
                                if v_isSharedCheck_1698_ == 0 {
                                    v___x_1693_ = v___x_1680_;
                                    v_isShared_1694_ = v_isSharedCheck_1698_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1691_);
                                    crate::leanh::lean_dec(v___x_1680_);
                                    v___x_1693_ = crate::leanh::lean_box(0);
                                    v_isShared_1694_ = v_isSharedCheck_1698_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                v_a_1699_ = crate::leanh::lean_ctor_get(v___x_1680_, 0);
                                crate::leanh::lean_inc(v_a_1699_);
                                crate::leanh::lean_dec_ref_known(v___x_1680_, 1);
                                if crate::leanh::lean_obj_tag(v_a_1699_) == 1 {
                                    crate::leanh::lean_dec(v_a_1670_);
                                    crate::leanh::lean_dec(v_val_1623_);
                                    v_val_1700_ = crate::leanh::lean_ctor_get(v_a_1699_, 0);
                                    crate::leanh::lean_inc(v_val_1700_);
                                    crate::leanh::lean_dec_ref_known(v_a_1699_, 1);
                                    v___x_1701_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3;
                                    v___x_1702_ =
                                        l_Lake_JsonObject_getJson_x3f(v_val_1700_, v___x_1701_);
                                    if crate::leanh::lean_obj_tag(v___x_1702_) == 0 {
                                        crate::leanh::lean_dec(v_val_1700_);
                                        v___x_1703_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__5;
                                        return v___x_1703_;
                                    } else {
                                        v_val_1704_ = crate::leanh::lean_ctor_get(v___x_1702_, 0);
                                        crate::leanh::lean_inc(v_val_1704_);
                                        crate::leanh::lean_dec_ref_known(v___x_1702_, 1);
                                        v___x_1705_ = l_Lean_Json_getNat_x3f(v_val_1704_);
                                        if crate::leanh::lean_obj_tag(v___x_1705_) == 0 {
                                            crate::leanh::lean_dec(v_val_1700_);
                                            v_a_1706_ = crate::leanh::lean_ctor_get(v___x_1705_, 0);
                                            v_isSharedCheck_1715_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1705_))
                                                    as u8;
                                            if v_isSharedCheck_1715_ == 0 {
                                                v___x_1708_ = v___x_1705_;
                                                v_isShared_1709_ = v_isSharedCheck_1715_;
                                                state = 17;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1706_);
                                                crate::leanh::lean_dec(v___x_1705_);
                                                v___x_1708_ = crate::leanh::lean_box(0);
                                                v_isShared_1709_ = v_isSharedCheck_1715_;
                                                state = 17;
                                                continue;
                                            }
                                        } else {
                                            if crate::leanh::lean_obj_tag(v___x_1705_) == 0 {
                                                crate::leanh::lean_dec(v_val_1700_);
                                                v_a_1716_ =
                                                    crate::leanh::lean_ctor_get(v___x_1705_, 0);
                                                v_isSharedCheck_1723_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_1705_))
                                                        as u8;
                                                if v_isSharedCheck_1723_ == 0 {
                                                    v___x_1718_ = v___x_1705_;
                                                    v_isShared_1719_ = v_isSharedCheck_1723_;
                                                    state = 19;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_1716_);
                                                    crate::leanh::lean_dec(v___x_1705_);
                                                    v___x_1718_ = crate::leanh::lean_box(0);
                                                    v_isShared_1719_ = v_isSharedCheck_1723_;
                                                    state = 19;
                                                    continue;
                                                }
                                            } else {
                                                v_a_1724_ =
                                                    crate::leanh::lean_ctor_get(v___x_1705_, 0);
                                                crate::leanh::lean_inc(v_a_1724_);
                                                crate::leanh::lean_dec_ref_known(v___x_1705_, 1);
                                                v___x_1725_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7;
                                                v___x_1726_ = l_Lake_JsonObject_getJson_x3f(
                                                    v_val_1700_,
                                                    v___x_1725_,
                                                );
                                                crate::leanh::lean_dec(v_val_1700_);
                                                if crate::leanh::lean_obj_tag(v___x_1726_) == 0 {
                                                    crate::leanh::lean_dec(v_a_1724_);
                                                    v___x_1727_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__9;
                                                    return v___x_1727_;
                                                } else {
                                                    v_val_1728_ =
                                                        crate::leanh::lean_ctor_get(v___x_1726_, 0);
                                                    crate::leanh::lean_inc(v_val_1728_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1726_,
                                                        1,
                                                    );
                                                    v___x_1729_ =
                                                        l_Lean_Json_getStr_x3f(v_val_1728_);
                                                    if crate::leanh::lean_obj_tag(v___x_1729_) == 0
                                                    {
                                                        crate::leanh::lean_dec(v_a_1724_);
                                                        v_a_1730_ = crate::leanh::lean_ctor_get(
                                                            v___x_1729_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_1739_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_1729_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_1739_ == 0 {
                                                            v___x_1732_ = v___x_1729_;
                                                            v_isShared_1733_ =
                                                                v_isSharedCheck_1739_;
                                                            state = 21;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_1730_);
                                                            crate::leanh::lean_dec(v___x_1729_);
                                                            v___x_1732_ = crate::leanh::lean_box(0);
                                                            v_isShared_1733_ =
                                                                v_isSharedCheck_1739_;
                                                            state = 21;
                                                            continue;
                                                        }
                                                    } else {
                                                        if crate::leanh::lean_obj_tag(v___x_1729_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec(v_a_1724_);
                                                            v_a_1740_ = crate::leanh::lean_ctor_get(
                                                                v___x_1729_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_1747_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_1729_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_1747_ == 0 {
                                                                v___x_1742_ = v___x_1729_;
                                                                v_isShared_1743_ =
                                                                    v_isSharedCheck_1747_;
                                                                state = 23;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_1740_);
                                                                crate::leanh::lean_dec(v___x_1729_);
                                                                v___x_1742_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_1743_ =
                                                                    v_isSharedCheck_1747_;
                                                                state = 23;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_1748_ = crate::leanh::lean_ctor_get(
                                                                v___x_1729_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_1756_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_1729_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_1756_ == 0 {
                                                                v___x_1750_ = v___x_1729_;
                                                                v_isShared_1751_ =
                                                                    v_isSharedCheck_1756_;
                                                                state = 25;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_1748_);
                                                                crate::leanh::lean_dec(v___x_1729_);
                                                                v___x_1750_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_1751_ =
                                                                    v_isSharedCheck_1756_;
                                                                state = 25;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1699_);
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1669_);
                    v___x_1757_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_1623_);
                    if crate::leanh::lean_obj_tag(v___x_1757_) == 0 {
                        v_a_1758_ = crate::leanh::lean_ctor_get(v___x_1757_, 0);
                        v_isSharedCheck_1765_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1757_)) as u8;
                        if v_isSharedCheck_1765_ == 0 {
                            v___x_1760_ = v___x_1757_;
                            v_isShared_1761_ = v_isSharedCheck_1765_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1758_);
                            crate::leanh::lean_dec(v___x_1757_);
                            v___x_1760_ = crate::leanh::lean_box(0);
                            v_isShared_1761_ = v_isSharedCheck_1765_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v_a_1766_ = crate::leanh::lean_ctor_get(v___x_1757_, 0);
                        v_isSharedCheck_1774_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1757_)) as u8;
                        if v_isSharedCheck_1774_ == 0 {
                            v___x_1768_ = v___x_1757_;
                            v_isShared_1769_ = v_isSharedCheck_1774_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1766_);
                            crate::leanh::lean_dec(v___x_1757_);
                            v___x_1768_ = crate::leanh::lean_box(0);
                            v_isShared_1769_ = v_isSharedCheck_1774_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1625_) == 1 {
                    crate::leanh::lean_dec(v_val_1623_);
                    v_val_1626_ = crate::leanh::lean_ctor_get(v_a_1625_, 0);
                    v_isSharedCheck_1650_ = (!crate::leanh::lean_is_exclusive(v_a_1625_)) as u8;
                    if v_isSharedCheck_1650_ == 0 {
                        v___x_1628_ = v_a_1625_;
                        v_isShared_1629_ = v_isSharedCheck_1650_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1626_);
                        crate::leanh::lean_dec(v_a_1625_);
                        v___x_1628_ = crate::leanh::lean_box(0);
                        v_isShared_1629_ = v_isSharedCheck_1650_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1625_);
                    v___x_1651_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_1623_);
                    if crate::leanh::lean_obj_tag(v___x_1651_) == 0 {
                        v_a_1652_ = crate::leanh::lean_ctor_get(v___x_1651_, 0);
                        v_isSharedCheck_1659_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1651_)) as u8;
                        if v_isSharedCheck_1659_ == 0 {
                            v___x_1654_ = v___x_1651_;
                            v_isShared_1655_ = v_isSharedCheck_1659_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1652_);
                            crate::leanh::lean_dec(v___x_1651_);
                            v___x_1654_ = crate::leanh::lean_box(0);
                            v_isShared_1655_ = v_isSharedCheck_1659_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_1660_ = crate::leanh::lean_ctor_get(v___x_1651_, 0);
                        v_isSharedCheck_1668_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1651_)) as u8;
                        if v_isSharedCheck_1668_ == 0 {
                            v___x_1662_ = v___x_1651_;
                            v_isShared_1663_ = v_isSharedCheck_1668_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1660_);
                            crate::leanh::lean_dec(v___x_1651_);
                            v___x_1662_ = crate::leanh::lean_box(0);
                            v_isShared_1663_ = v_isSharedCheck_1668_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_1630_ = l_Lake_RegistryPkg_fromJson_x3f(v_val_1626_);
                if crate::leanh::lean_obj_tag(v___x_1630_) == 0 {
                    crate::leanh::lean_del_object(v___x_1628_);
                    v_a_1631_ = crate::leanh::lean_ctor_get(v___x_1630_, 0);
                    v_isSharedCheck_1638_ = (!crate::leanh::lean_is_exclusive(v___x_1630_)) as u8;
                    if v_isSharedCheck_1638_ == 0 {
                        v___x_1633_ = v___x_1630_;
                        v_isShared_1634_ = v_isSharedCheck_1638_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1631_);
                        crate::leanh::lean_dec(v___x_1630_);
                        v___x_1633_ = crate::leanh::lean_box(0);
                        v_isShared_1634_ = v_isSharedCheck_1638_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1639_ = crate::leanh::lean_ctor_get(v___x_1630_, 0);
                    v_isSharedCheck_1649_ = (!crate::leanh::lean_is_exclusive(v___x_1630_)) as u8;
                    if v_isSharedCheck_1649_ == 0 {
                        v___x_1641_ = v___x_1630_;
                        v_isShared_1642_ = v_isSharedCheck_1649_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1639_);
                        crate::leanh::lean_dec(v___x_1630_);
                        v___x_1641_ = crate::leanh::lean_box(0);
                        v_isShared_1642_ = v_isSharedCheck_1649_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1634_ == 0 {
                    v___x_1636_ = v___x_1633_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1637_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
                    v___x_1636_ = v_reuseFailAlloc_1637_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1636_;
            }
            5 => {
                if v_isShared_1629_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1628_, 0);
                    crate::leanh::lean_ctor_set(v___x_1628_, 0, v_a_1639_);
                    v___x_1644_ = v___x_1628_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1648_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1639_);
                    v___x_1644_ = v_reuseFailAlloc_1648_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1642_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1641_, 0, v___x_1644_);
                    v___x_1646_ = v___x_1641_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1647_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
                    v___x_1646_ = v_reuseFailAlloc_1647_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1646_;
            }
            8 => {
                if v_isShared_1655_ == 0 {
                    v___x_1657_ = v___x_1654_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
                    v___x_1657_ = v_reuseFailAlloc_1658_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1657_;
            }
            10 => {
                v___x_1664_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1664_, 0, v_a_1660_);
                if v_isShared_1663_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1662_, 0, v___x_1664_);
                    v___x_1666_ = v___x_1662_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
                    v___x_1666_ = v_reuseFailAlloc_1667_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1666_;
            }
            12 => {
                v___x_1672_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0;
                v___x_1673_ = l_Lake_JsonObject_getJson_x3f(v_a_1670_, v___x_1672_);
                crate::leanh::lean_dec(v_a_1670_);
                if crate::leanh::lean_obj_tag(v___x_1673_) == 0 {
                    v_a_1625_ = v___x_1673_;
                    state = 1;
                    continue;
                } else {
                    v_val_1674_ = crate::leanh::lean_ctor_get(v___x_1673_, 0);
                    crate::leanh::lean_inc(v_val_1674_);
                    crate::leanh::lean_dec_ref_known(v___x_1673_, 1);
                    v___x_1675_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_1674_);
                    v_a_1676_ = crate::leanh::lean_ctor_get(v___x_1675_, 0);
                    crate::leanh::lean_inc(v_a_1676_);
                    crate::leanh::lean_dec_ref(v___x_1675_);
                    v_a_1625_ = v_a_1676_;
                    state = 1;
                    continue;
                }
            }
            13 => {
                v___x_1685_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2;
                v___x_1686_ = lean_string_append(v___x_1685_, v_a_1681_);
                crate::leanh::lean_dec(v_a_1681_);
                if v_isShared_1684_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1683_, 0, v___x_1686_);
                    v___x_1688_ = v___x_1683_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
                    v___x_1688_ = v_reuseFailAlloc_1689_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1688_;
            }
            15 => {
                if v_isShared_1694_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1693_, 0);
                    v___x_1696_ = v___x_1693_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
                    v___x_1696_ = v_reuseFailAlloc_1697_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1696_;
            }
            17 => {
                v___x_1710_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6;
                v___x_1711_ = lean_string_append(v___x_1710_, v_a_1706_);
                crate::leanh::lean_dec(v_a_1706_);
                if v_isShared_1709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1708_, 0, v___x_1711_);
                    v___x_1713_ = v___x_1708_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
                    v___x_1713_ = v_reuseFailAlloc_1714_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1713_;
            }
            19 => {
                if v_isShared_1719_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1718_, 0);
                    v___x_1721_ = v___x_1718_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1722_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
                    v___x_1721_ = v_reuseFailAlloc_1722_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1721_;
            }
            21 => {
                v___x_1734_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10;
                v___x_1735_ = lean_string_append(v___x_1734_, v_a_1730_);
                crate::leanh::lean_dec(v_a_1730_);
                if v_isShared_1733_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1732_, 0, v___x_1735_);
                    v___x_1737_ = v___x_1732_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
                    v___x_1737_ = v_reuseFailAlloc_1738_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1737_;
            }
            23 => {
                if v_isShared_1743_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1742_, 0);
                    v___x_1745_ = v___x_1742_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
                    v___x_1745_ = v_reuseFailAlloc_1746_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1745_;
            }
            25 => {
                v___x_1752_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1752_, 0, v_a_1724_);
                crate::leanh::lean_ctor_set(v___x_1752_, 1, v_a_1748_);
                if v_isShared_1751_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1750_, 0, v___x_1752_);
                    v___x_1754_ = v___x_1750_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1755_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
                    v___x_1754_ = v_reuseFailAlloc_1755_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1754_;
            }
            27 => {
                if v_isShared_1761_ == 0 {
                    v___x_1763_ = v___x_1760_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
                    v___x_1763_ = v_reuseFailAlloc_1764_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1763_;
            }
            29 => {
                v___x_1770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1770_, 0, v_a_1766_);
                if v_isShared_1769_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1768_, 0, v___x_1770_);
                    v___x_1772_ = v___x_1768_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
                    v___x_1772_ = v_reuseFailAlloc_1773_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_1772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Reservoir_fetchPkg_x3f(
    mut v_lakeEnv_1780_: *mut crate::leanh::LeanObject,
    mut v_owner_1781_: *mut crate::leanh::LeanObject,
    mut v_pkg_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_url_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1857_: u8 = 0;
    let mut v_status_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: u8 = 0;
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: u8 = 0;
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut v_a_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_pkg_1782_);
                crate::leanh::lean_inc_ref(v_owner_1781_);
                v_url_1785_ =
                    l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1780_, v_owner_1781_, v_pkg_1782_);
                v___x_1786_ = l_Lake_Reservoir_lakeHeaders;
                v___x_1787_ = l_Lake_getUrl(v_url_1785_, v___x_1786_, v_a_1783_);
                if crate::leanh::lean_obj_tag(v___x_1787_) == 0 {
                    v_a_1788_ = crate::leanh::lean_ctor_get(v___x_1787_, 0);
                    v_a_1789_ = crate::leanh::lean_ctor_get(v___x_1787_, 1);
                    v_isSharedCheck_1879_ = (!crate::leanh::lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v___x_1791_ = v___x_1787_;
                        v_isShared_1792_ = v_isSharedCheck_1879_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1789_);
                        crate::leanh::lean_inc(v_a_1788_);
                        crate::leanh::lean_dec(v___x_1787_);
                        v___x_1791_ = crate::leanh::lean_box(0);
                        v_isShared_1792_ = v_isSharedCheck_1879_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1880_ = crate::leanh::lean_ctor_get(v___x_1787_, 0);
                    v_a_1881_ = crate::leanh::lean_ctor_get(v___x_1787_, 1);
                    v_isSharedCheck_1896_ = (!crate::leanh::lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1896_ == 0 {
                        v___x_1883_ = v___x_1787_;
                        v_isShared_1884_ = v_isSharedCheck_1896_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1881_);
                        crate::leanh::lean_inc(v_a_1880_);
                        crate::leanh::lean_dec(v___x_1787_);
                        v___x_1883_ = crate::leanh::lean_box(0);
                        v_isShared_1884_ = v_isSharedCheck_1896_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1788_);
                v___x_1793_ = l_Lean_Json_parse(v_a_1788_);
                if crate::leanh::lean_obj_tag(v___x_1793_) == 0 {
                    v_a_1794_ = crate::leanh::lean_ctor_get(v___x_1793_, 0);
                    crate::leanh::lean_inc(v_a_1794_);
                    crate::leanh::lean_dec_ref_known(v___x_1793_, 1);
                    v___x_1795_ = l_Lake_Reservoir_pkgApiUrl___closed__1;
                    v___x_1796_ = lean_string_append(v_owner_1781_, v___x_1795_);
                    v___x_1797_ = lean_string_append(v___x_1796_, v_pkg_1782_);
                    crate::leanh::lean_dec_ref(v_pkg_1782_);
                    v___x_1798_ = l_Lake_Reservoir_fetchPkg_x3f___closed__0;
                    crate::leanh::lean_inc_ref(v___x_1797_);
                    v___x_1799_ = lean_string_append(v___x_1797_, v___x_1798_);
                    v___x_1800_ = lean_string_append(v___x_1799_, v_a_1794_);
                    crate::leanh::lean_dec(v_a_1794_);
                    v___x_1801_ = 3;
                    v___x_1802_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1802_, 0, v___x_1800_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1802_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1801_,
                    );
                    v___x_1803_ = lean_array_get_size(v_a_1789_);
                    v___x_1804_ = lean_array_push(v_a_1789_, v___x_1802_);
                    v___x_1805_ = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
                    v___x_1806_ = lean_string_append(v___x_1797_, v___x_1805_);
                    v___x_1807_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1808_ = lean_string_utf8_byte_size(v_a_1788_);
                    v___x_1809_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1809_, 0, v_a_1788_);
                    crate::leanh::lean_ctor_set(v___x_1809_, 1, v___x_1807_);
                    crate::leanh::lean_ctor_set(v___x_1809_, 2, v___x_1808_);
                    v___x_1810_ = l_String_Slice_trimAscii(v___x_1809_);
                    v___x_1811_ = l_String_Slice_toString(v___x_1810_);
                    crate::leanh::lean_dec_ref(v___x_1810_);
                    v___x_1812_ = lean_string_append(v___x_1806_, v___x_1811_);
                    crate::leanh::lean_dec_ref(v___x_1811_);
                    v___x_1813_ = 0;
                    v___x_1814_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1814_, 0, v___x_1812_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1814_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1813_,
                    );
                    v___x_1815_ = lean_array_push(v___x_1804_, v___x_1814_);
                    if v_isShared_1792_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1791_, 1);
                        crate::leanh::lean_ctor_set(v___x_1791_, 1, v___x_1815_);
                        crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1803_);
                        v___x_1817_ = v___x_1791_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1818_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1803_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1815_);
                        v___x_1817_ = v_reuseFailAlloc_1818_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1819_ = crate::leanh::lean_ctor_get(v___x_1793_, 0);
                    crate::leanh::lean_inc(v_a_1819_);
                    crate::leanh::lean_dec_ref_known(v___x_1793_, 1);
                    v___x_1820_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0(v_a_1819_);
                    if crate::leanh::lean_obj_tag(v___x_1820_) == 0 {
                        v_a_1821_ = crate::leanh::lean_ctor_get(v___x_1820_, 0);
                        crate::leanh::lean_inc(v_a_1821_);
                        crate::leanh::lean_dec_ref_known(v___x_1820_, 1);
                        v___x_1822_ = l_Lake_Reservoir_pkgApiUrl___closed__1;
                        v___x_1823_ = lean_string_append(v_owner_1781_, v___x_1822_);
                        v___x_1824_ = lean_string_append(v___x_1823_, v_pkg_1782_);
                        crate::leanh::lean_dec_ref(v_pkg_1782_);
                        v___x_1825_ = l_Lake_Reservoir_fetchPkg_x3f___closed__2;
                        crate::leanh::lean_inc_ref(v___x_1824_);
                        v___x_1826_ = lean_string_append(v___x_1824_, v___x_1825_);
                        v___x_1827_ = lean_string_append(v___x_1826_, v_a_1821_);
                        crate::leanh::lean_dec(v_a_1821_);
                        v___x_1828_ = 3;
                        v___x_1829_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1829_, 0, v___x_1827_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1829_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1828_,
                        );
                        v___x_1830_ = lean_array_get_size(v_a_1789_);
                        v___x_1831_ = lean_array_push(v_a_1789_, v___x_1829_);
                        v___x_1832_ = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
                        v___x_1833_ = lean_string_append(v___x_1824_, v___x_1832_);
                        v___x_1834_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1835_ = lean_string_utf8_byte_size(v_a_1788_);
                        v___x_1836_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1836_, 0, v_a_1788_);
                        crate::leanh::lean_ctor_set(v___x_1836_, 1, v___x_1834_);
                        crate::leanh::lean_ctor_set(v___x_1836_, 2, v___x_1835_);
                        v___x_1837_ = l_String_Slice_trimAscii(v___x_1836_);
                        v___x_1838_ = l_String_Slice_toString(v___x_1837_);
                        crate::leanh::lean_dec_ref(v___x_1837_);
                        v___x_1839_ = lean_string_append(v___x_1833_, v___x_1838_);
                        crate::leanh::lean_dec_ref(v___x_1838_);
                        v___x_1840_ = 0;
                        v___x_1841_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1841_, 0, v___x_1839_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1841_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1840_,
                        );
                        v___x_1842_ = lean_array_push(v___x_1831_, v___x_1841_);
                        if v_isShared_1792_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1791_, 1);
                            crate::leanh::lean_ctor_set(v___x_1791_, 1, v___x_1842_);
                            crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1830_);
                            v___x_1844_ = v___x_1791_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1845_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1830_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1842_);
                            v___x_1844_ = v_reuseFailAlloc_1845_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1788_);
                        v_a_1846_ = crate::leanh::lean_ctor_get(v___x_1820_, 0);
                        crate::leanh::lean_inc(v_a_1846_);
                        crate::leanh::lean_dec_ref_known(v___x_1820_, 1);
                        if crate::leanh::lean_obj_tag(v_a_1846_) == 0 {
                            crate::leanh::lean_dec_ref(v_pkg_1782_);
                            crate::leanh::lean_dec_ref(v_owner_1781_);
                            v_a_1847_ = crate::leanh::lean_ctor_get(v_a_1846_, 0);
                            v_isSharedCheck_1857_ =
                                (!crate::leanh::lean_is_exclusive(v_a_1846_)) as u8;
                            if v_isSharedCheck_1857_ == 0 {
                                v___x_1849_ = v_a_1846_;
                                v_isShared_1850_ = v_isSharedCheck_1857_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1847_);
                                crate::leanh::lean_dec(v_a_1846_);
                                v___x_1849_ = crate::leanh::lean_box(0);
                                v_isShared_1850_ = v_isSharedCheck_1857_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_status_1858_ = crate::leanh::lean_ctor_get(v_a_1846_, 0);
                            crate::leanh::lean_inc(v_status_1858_);
                            v_message_1859_ = crate::leanh::lean_ctor_get(v_a_1846_, 1);
                            crate::leanh::lean_inc_ref(v_message_1859_);
                            crate::leanh::lean_dec_ref_known(v_a_1846_, 2);
                            v___x_1860_ = crate::leanh::lean_unsigned_to_nat(404);
                            v___x_1861_ = lean_nat_dec_eq(v_status_1858_, v___x_1860_);
                            crate::leanh::lean_dec(v_status_1858_);
                            if v___x_1861_ == 0 {
                                v___x_1862_ = l_Lake_Reservoir_pkgApiUrl___closed__1;
                                v___x_1863_ = lean_string_append(v_owner_1781_, v___x_1862_);
                                v___x_1864_ = lean_string_append(v___x_1863_, v_pkg_1782_);
                                crate::leanh::lean_dec_ref(v_pkg_1782_);
                                v___x_1865_ = l_Lake_Reservoir_fetchPkg_x3f___closed__3;
                                v___x_1866_ = lean_string_append(v___x_1864_, v___x_1865_);
                                v___x_1867_ = lean_string_append(v___x_1866_, v_message_1859_);
                                crate::leanh::lean_dec_ref(v_message_1859_);
                                v___x_1868_ = 3;
                                v___x_1869_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_1869_, 0, v___x_1867_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_1869_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_1868_,
                                );
                                v___x_1870_ = lean_array_get_size(v_a_1789_);
                                v___x_1871_ = lean_array_push(v_a_1789_, v___x_1869_);
                                if v_isShared_1792_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_1791_, 1);
                                    crate::leanh::lean_ctor_set(v___x_1791_, 1, v___x_1871_);
                                    crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1870_);
                                    v___x_1873_ = v___x_1791_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1874_ =
                                        crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1874_,
                                        0,
                                        v___x_1870_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1874_,
                                        1,
                                        v___x_1871_,
                                    );
                                    v___x_1873_ = v_reuseFailAlloc_1874_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_message_1859_);
                                crate::leanh::lean_dec_ref(v_pkg_1782_);
                                crate::leanh::lean_dec_ref(v_owner_1781_);
                                v___x_1875_ = crate::leanh::lean_box(0);
                                if v_isShared_1792_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1875_);
                                    v___x_1877_ = v___x_1791_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1878_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1878_,
                                        0,
                                        v___x_1875_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1878_,
                                        1,
                                        v_a_1789_,
                                    );
                                    v___x_1877_ = v_reuseFailAlloc_1878_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1817_;
            }
            3 => {
                return v___x_1844_;
            }
            4 => {
                if v_isShared_1850_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1849_, 1);
                    v___x_1852_ = v___x_1849_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1856_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1847_);
                    v___x_1852_ = v_reuseFailAlloc_1856_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1792_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1852_);
                    v___x_1854_ = v___x_1791_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1855_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_a_1789_);
                    v___x_1854_ = v_reuseFailAlloc_1855_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1854_;
            }
            7 => {
                return v___x_1873_;
            }
            8 => {
                return v___x_1877_;
            }
            9 => {
                v___x_1885_ = l_Lake_Reservoir_pkgApiUrl___closed__1;
                v___x_1886_ = lean_string_append(v_owner_1781_, v___x_1885_);
                v___x_1887_ = lean_string_append(v___x_1886_, v_pkg_1782_);
                crate::leanh::lean_dec_ref(v_pkg_1782_);
                v___x_1888_ = l_Lake_Reservoir_fetchPkg_x3f___closed__4;
                v___x_1889_ = lean_string_append(v___x_1887_, v___x_1888_);
                v___x_1890_ = 3;
                v___x_1891_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1891_, 0, v___x_1889_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1891_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1890_,
                );
                v___x_1892_ = lean_array_push(v_a_1881_, v___x_1891_);
                if v_isShared_1884_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1883_, 1, v___x_1892_);
                    v___x_1894_ = v___x_1883_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1895_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1892_);
                    v___x_1894_ = v_reuseFailAlloc_1895_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Reservoir_fetchPkg_x3f___boxed(
    mut v_lakeEnv_1897_: *mut crate::leanh::LeanObject,
    mut v_owner_1898_: *mut crate::leanh::LeanObject,
    mut v_pkg_1899_: *mut crate::leanh::LeanObject,
    mut v_a_1900_: *mut crate::leanh::LeanObject,
    mut v_a_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ =
        l_Lake_Reservoir_fetchPkg_x3f(v_lakeEnv_1897_, v_owner_1898_, v_pkg_1899_, v_a_1900_);
    return v_res_1902_;
}
pub unsafe fn l_Lake_RegistryVer_fromJson_x3f(
    mut v_val_1910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1945_: u8 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1920_ = l_Lean_Json_getObj_x3f(v_val_1910_);
                if crate::leanh::lean_obj_tag(v___x_1920_) == 0 {
                    v_a_1921_ = crate::leanh::lean_ctor_get(v___x_1920_, 0);
                    crate::leanh::lean_inc(v_a_1921_);
                    crate::leanh::lean_dec_ref_known(v___x_1920_, 1);
                    v_a_1912_ = v_a_1921_;
                    state = 1;
                    continue;
                } else {
                    v_a_1922_ = crate::leanh::lean_ctor_get(v___x_1920_, 0);
                    crate::leanh::lean_inc(v_a_1922_);
                    crate::leanh::lean_dec_ref_known(v___x_1920_, 1);
                    v___x_1923_ = l_Lake_RegistryVer_fromJson_x3f___closed__2;
                    v___x_1924_ = l_Lake_JsonObject_getJson_x3f(v_a_1922_, v___x_1923_);
                    if crate::leanh::lean_obj_tag(v___x_1924_) == 0 {
                        crate::leanh::lean_dec(v_a_1922_);
                        v___x_1925_ = l_Lake_RegistryVer_fromJson_x3f___closed__3;
                        v_a_1912_ = v___x_1925_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1926_ = crate::leanh::lean_ctor_get(v___x_1924_, 0);
                        crate::leanh::lean_inc(v_val_1926_);
                        crate::leanh::lean_dec_ref_known(v___x_1924_, 1);
                        v___x_1927_ = l_Lean_Json_getStr_x3f(v_val_1926_);
                        if crate::leanh::lean_obj_tag(v___x_1927_) == 0 {
                            crate::leanh::lean_dec(v_a_1922_);
                            v_a_1928_ = crate::leanh::lean_ctor_get(v___x_1927_, 0);
                            crate::leanh::lean_inc(v_a_1928_);
                            crate::leanh::lean_dec_ref_known(v___x_1927_, 1);
                            v_a_1917_ = v_a_1928_;
                            state = 2;
                            continue;
                        } else {
                            v_a_1929_ = crate::leanh::lean_ctor_get(v___x_1927_, 0);
                            crate::leanh::lean_inc(v_a_1929_);
                            crate::leanh::lean_dec_ref_known(v___x_1927_, 1);
                            v___x_1930_ = l_Lake_StdVer_parse(v_a_1929_);
                            if crate::leanh::lean_obj_tag(v___x_1930_) == 0 {
                                crate::leanh::lean_dec(v_a_1922_);
                                v_a_1931_ = crate::leanh::lean_ctor_get(v___x_1930_, 0);
                                crate::leanh::lean_inc(v_a_1931_);
                                crate::leanh::lean_dec_ref_known(v___x_1930_, 1);
                                v_a_1917_ = v_a_1931_;
                                state = 2;
                                continue;
                            } else {
                                v_a_1932_ = crate::leanh::lean_ctor_get(v___x_1930_, 0);
                                crate::leanh::lean_inc(v_a_1932_);
                                crate::leanh::lean_dec_ref_known(v___x_1930_, 1);
                                v___x_1933_ = l_Lake_RegistryVer_fromJson_x3f___closed__4;
                                v___x_1934_ = l_Lake_JsonObject_getJson_x3f(v_a_1922_, v___x_1933_);
                                crate::leanh::lean_dec(v_a_1922_);
                                if crate::leanh::lean_obj_tag(v___x_1934_) == 0 {
                                    crate::leanh::lean_dec(v_a_1932_);
                                    v___x_1935_ = l_Lake_RegistryVer_fromJson_x3f___closed__5;
                                    v_a_1912_ = v___x_1935_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_1936_ = crate::leanh::lean_ctor_get(v___x_1934_, 0);
                                    crate::leanh::lean_inc(v_val_1936_);
                                    crate::leanh::lean_dec_ref_known(v___x_1934_, 1);
                                    v___x_1937_ = l_Lean_Json_getStr_x3f(v_val_1936_);
                                    if crate::leanh::lean_obj_tag(v___x_1937_) == 0 {
                                        crate::leanh::lean_dec(v_a_1932_);
                                        v_a_1938_ = crate::leanh::lean_ctor_get(v___x_1937_, 0);
                                        crate::leanh::lean_inc(v_a_1938_);
                                        crate::leanh::lean_dec_ref_known(v___x_1937_, 1);
                                        v___x_1939_ = l_Lake_RegistryVer_fromJson_x3f___closed__6;
                                        v___x_1940_ = lean_string_append(v___x_1939_, v_a_1938_);
                                        crate::leanh::lean_dec(v_a_1938_);
                                        v_a_1912_ = v___x_1940_;
                                        state = 1;
                                        continue;
                                    } else {
                                        if crate::leanh::lean_obj_tag(v___x_1937_) == 0 {
                                            crate::leanh::lean_dec(v_a_1932_);
                                            v_a_1941_ = crate::leanh::lean_ctor_get(v___x_1937_, 0);
                                            crate::leanh::lean_inc(v_a_1941_);
                                            crate::leanh::lean_dec_ref_known(v___x_1937_, 1);
                                            v_a_1912_ = v_a_1941_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_1942_ = crate::leanh::lean_ctor_get(v___x_1937_, 0);
                                            v_isSharedCheck_1950_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1937_))
                                                    as u8;
                                            if v_isSharedCheck_1950_ == 0 {
                                                v___x_1944_ = v___x_1937_;
                                                v_isShared_1945_ = v_isSharedCheck_1950_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1942_);
                                                crate::leanh::lean_dec(v___x_1937_);
                                                v___x_1944_ = crate::leanh::lean_box(0);
                                                v_isShared_1945_ = v_isSharedCheck_1950_;
                                                state = 3;
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
            1 => {
                v___x_1913_ = l_Lake_RegistryVer_fromJson_x3f___closed__0;
                v___x_1914_ = lean_string_append(v___x_1913_, v_a_1912_);
                crate::leanh::lean_dec_ref(v_a_1912_);
                v___x_1915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1915_, 0, v___x_1914_);
                return v___x_1915_;
            }
            2 => {
                v___x_1918_ = l_Lake_RegistryVer_fromJson_x3f___closed__1;
                v___x_1919_ = lean_string_append(v___x_1918_, v_a_1917_);
                crate::leanh::lean_dec_ref(v_a_1917_);
                v_a_1912_ = v___x_1919_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1946_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1946_, 0, v_a_1932_);
                crate::leanh::lean_ctor_set(v___x_1946_, 1, v_a_1942_);
                if v_isShared_1945_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1944_, 0, v___x_1946_);
                    v___x_1948_ = v___x_1944_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1949_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
                    v___x_1948_ = v_reuseFailAlloc_1949_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Reservoir_pkgVersionsApiUrl(
    mut v_lakeEnv_1954_: *mut crate::leanh::LeanObject,
    mut v_owner_1955_: *mut crate::leanh::LeanObject,
    mut v_pkg_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_reservoirApiUrl_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_reservoirApiUrl_1957_ = crate::leanh::lean_ctor_get(v_lakeEnv_1954_, 3);
    crate::leanh::lean_inc_ref(v_reservoirApiUrl_1957_);
    crate::leanh::lean_dec_ref(v_lakeEnv_1954_);
    v___x_1958_ = l_Lake_Reservoir_pkgApiUrl___closed__0;
    v___x_1959_ = lean_string_append(v_reservoirApiUrl_1957_, v___x_1958_);
    v___x_1960_ = l_Lake_instInhabitedRegistrySrc_default___closed__0;
    v___x_1961_ = l_Lake_uriEncode(v_owner_1955_, v___x_1960_);
    v___x_1962_ = lean_string_append(v___x_1959_, v___x_1961_);
    crate::leanh::lean_dec_ref(v___x_1961_);
    v___x_1963_ = l_Lake_Reservoir_pkgApiUrl___closed__1;
    v___x_1964_ = lean_string_append(v___x_1962_, v___x_1963_);
    v___x_1965_ = l_Lake_uriEncode(v_pkg_1956_, v___x_1960_);
    v___x_1966_ = lean_string_append(v___x_1964_, v___x_1965_);
    crate::leanh::lean_dec_ref(v___x_1965_);
    v___x_1967_ = l_Lake_Reservoir_pkgVersionsApiUrl___closed__0;
    v___x_1968_ = lean_string_append(v___x_1966_, v___x_1967_);
    return v___x_1968_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(
    mut v_sz_1969_: usize,
    mut v_i_1970_: usize,
    mut v_bs_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1972_: u8 = 0;
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_a_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: usize = 0;
    let mut v___x_1988_: usize = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1972_ = lean_usize_dec_lt(v_i_1970_, v_sz_1969_);
                if v___x_1972_ == 0 {
                    v___x_1973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1973_, 0, v_bs_1971_);
                    return v___x_1973_;
                } else {
                    v_v_1974_ = lean_array_uget_borrowed(v_bs_1971_, v_i_1970_);
                    crate::leanh::lean_inc(v_v_1974_);
                    v___x_1975_ = l_Lake_RegistryVer_fromJson_x3f(v_v_1974_);
                    if crate::leanh::lean_obj_tag(v___x_1975_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_1971_);
                        v_a_1976_ = crate::leanh::lean_ctor_get(v___x_1975_, 0);
                        v_isSharedCheck_1983_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1975_)) as u8;
                        if v_isSharedCheck_1983_ == 0 {
                            v___x_1978_ = v___x_1975_;
                            v_isShared_1979_ = v_isSharedCheck_1983_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1976_);
                            crate::leanh::lean_dec(v___x_1975_);
                            v___x_1978_ = crate::leanh::lean_box(0);
                            v_isShared_1979_ = v_isSharedCheck_1983_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1984_ = crate::leanh::lean_ctor_get(v___x_1975_, 0);
                        crate::leanh::lean_inc(v_a_1984_);
                        crate::leanh::lean_dec_ref_known(v___x_1975_, 1);
                        v___x_1985_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1986_ = lean_array_uset(v_bs_1971_, v_i_1970_, v___x_1985_);
                        v___x_1987_ = 1usize;
                        v___x_1988_ = lean_usize_add(v_i_1970_, v___x_1987_);
                        v___x_1989_ = lean_array_uset(v_bs_x27_1986_, v_i_1970_, v_a_1984_);
                        v_i_1970_ = v___x_1988_;
                        v_bs_1971_ = v___x_1989_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1979_ == 0 {
                    v___x_1981_ = v___x_1978_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
                    v___x_1981_ = v_reuseFailAlloc_1982_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1___boxed(
    mut v_sz_1991_: *mut crate::leanh::LeanObject,
    mut v_i_1992_: *mut crate::leanh::LeanObject,
    mut v_bs_1993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1994_: usize = 0;
    let mut v_i_boxed_1995_: usize = 0;
    let mut v_res_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1994_ = crate::leanh::lean_unbox_usize(v_sz_1991_);
    crate::leanh::lean_dec(v_sz_1991_);
    v_i_boxed_1995_ = crate::leanh::lean_unbox_usize(v_i_1992_);
    crate::leanh::lean_dec(v_i_1992_);
    v_res_1996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_boxed_1994_, v_i_boxed_1995_, v_bs_1993_);
    return v_res_1996_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(
    mut v_x_1997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1997_) == 4 {
        let mut v_elems_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1999_: usize = 0;
        let mut v___x_2000_: usize = 0;
        let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_1998_ = crate::leanh::lean_ctor_get(v_x_1997_, 0);
        crate::leanh::lean_inc_ref(v_elems_1998_);
        crate::leanh::lean_dec_ref_known(v_x_1997_, 1);
        v_sz_1999_ = lean_array_size(v_elems_1998_);
        v___x_2000_ = 0usize;
        v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0_spec__1(v_sz_1999_, v___x_2000_, v_elems_1998_);
        return v___x_2001_;
    } else {
        let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2002_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__0;
        v___x_2003_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_2004_ = l_Lean_Json_pretty(v_x_1997_, v___x_2003_);
        v___x_2005_ = lean_string_append(v___x_2002_, v___x_2004_);
        crate::leanh::lean_dec_ref(v___x_2004_);
        v___x_2006_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_RegistryPkg_fromJson_x3f_spec__1_spec__1___closed__1;
        v___x_2007_ = lean_string_append(v___x_2005_, v___x_2006_);
        v___x_2008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2008_, 0, v___x_2007_);
        return v___x_2008_;
    }
}
pub unsafe fn l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(
    mut v_val_2013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2024_: u8 = 0;
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2028_: u8 = 0;
    let mut v_a_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_isSharedCheck_2040_: u8 = 0;
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2045_: u8 = 0;
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut v_a_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2053_: u8 = 0;
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2074_: u8 = 0;
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v_a_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2084_: u8 = 0;
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_a_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2099_: u8 = 0;
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2105_: u8 = 0;
    let mut v_a_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2113_: u8 = 0;
    let mut v_a_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2129_: u8 = 0;
    let mut v_a_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut v_a_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2141_: u8 = 0;
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2151_: u8 = 0;
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut v_a_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2159_: u8 = 0;
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_val_2013_);
                v___x_2059_ = l_Lean_Json_getObj_x3f(v_val_2013_);
                if crate::leanh::lean_obj_tag(v___x_2059_) == 1 {
                    v_a_2060_ = crate::leanh::lean_ctor_get(v___x_2059_, 0);
                    crate::leanh::lean_inc(v_a_2060_);
                    crate::leanh::lean_dec_ref_known(v___x_2059_, 1);
                    v___x_2067_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__1;
                    v___x_2068_ = l_Lake_JsonObject_getJson_x3f(v_a_2060_, v___x_2067_);
                    if crate::leanh::lean_obj_tag(v___x_2068_) == 0 {
                        state = 12;
                        continue;
                    } else {
                        v_val_2069_ = crate::leanh::lean_ctor_get(v___x_2068_, 0);
                        crate::leanh::lean_inc(v_val_2069_);
                        crate::leanh::lean_dec_ref_known(v___x_2068_, 1);
                        v___x_2070_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__1(v_val_2069_);
                        if crate::leanh::lean_obj_tag(v___x_2070_) == 0 {
                            crate::leanh::lean_dec(v_a_2060_);
                            crate::leanh::lean_dec(v_val_2013_);
                            v_a_2071_ = crate::leanh::lean_ctor_get(v___x_2070_, 0);
                            v_isSharedCheck_2080_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2070_)) as u8;
                            if v_isSharedCheck_2080_ == 0 {
                                v___x_2073_ = v___x_2070_;
                                v_isShared_2074_ = v_isSharedCheck_2080_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2071_);
                                crate::leanh::lean_dec(v___x_2070_);
                                v___x_2073_ = crate::leanh::lean_box(0);
                                v_isShared_2074_ = v_isSharedCheck_2080_;
                                state = 13;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_2070_) == 0 {
                                crate::leanh::lean_dec(v_a_2060_);
                                crate::leanh::lean_dec(v_val_2013_);
                                v_a_2081_ = crate::leanh::lean_ctor_get(v___x_2070_, 0);
                                v_isSharedCheck_2088_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2070_)) as u8;
                                if v_isSharedCheck_2088_ == 0 {
                                    v___x_2083_ = v___x_2070_;
                                    v_isShared_2084_ = v_isSharedCheck_2088_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2081_);
                                    crate::leanh::lean_dec(v___x_2070_);
                                    v___x_2083_ = crate::leanh::lean_box(0);
                                    v_isShared_2084_ = v_isSharedCheck_2088_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                v_a_2089_ = crate::leanh::lean_ctor_get(v___x_2070_, 0);
                                crate::leanh::lean_inc(v_a_2089_);
                                crate::leanh::lean_dec_ref_known(v___x_2070_, 1);
                                if crate::leanh::lean_obj_tag(v_a_2089_) == 1 {
                                    crate::leanh::lean_dec(v_a_2060_);
                                    crate::leanh::lean_dec(v_val_2013_);
                                    v_val_2090_ = crate::leanh::lean_ctor_get(v_a_2089_, 0);
                                    crate::leanh::lean_inc(v_val_2090_);
                                    crate::leanh::lean_dec_ref_known(v_a_2089_, 1);
                                    v___x_2091_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__3;
                                    v___x_2092_ =
                                        l_Lake_JsonObject_getJson_x3f(v_val_2090_, v___x_2091_);
                                    if crate::leanh::lean_obj_tag(v___x_2092_) == 0 {
                                        crate::leanh::lean_dec(v_val_2090_);
                                        v___x_2093_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__0;
                                        return v___x_2093_;
                                    } else {
                                        v_val_2094_ = crate::leanh::lean_ctor_get(v___x_2092_, 0);
                                        crate::leanh::lean_inc(v_val_2094_);
                                        crate::leanh::lean_dec_ref_known(v___x_2092_, 1);
                                        v___x_2095_ = l_Lean_Json_getNat_x3f(v_val_2094_);
                                        if crate::leanh::lean_obj_tag(v___x_2095_) == 0 {
                                            crate::leanh::lean_dec(v_val_2090_);
                                            v_a_2096_ = crate::leanh::lean_ctor_get(v___x_2095_, 0);
                                            v_isSharedCheck_2105_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2095_))
                                                    as u8;
                                            if v_isSharedCheck_2105_ == 0 {
                                                v___x_2098_ = v___x_2095_;
                                                v_isShared_2099_ = v_isSharedCheck_2105_;
                                                state = 17;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2096_);
                                                crate::leanh::lean_dec(v___x_2095_);
                                                v___x_2098_ = crate::leanh::lean_box(0);
                                                v_isShared_2099_ = v_isSharedCheck_2105_;
                                                state = 17;
                                                continue;
                                            }
                                        } else {
                                            if crate::leanh::lean_obj_tag(v___x_2095_) == 0 {
                                                crate::leanh::lean_dec(v_val_2090_);
                                                v_a_2106_ =
                                                    crate::leanh::lean_ctor_get(v___x_2095_, 0);
                                                v_isSharedCheck_2113_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2095_))
                                                        as u8;
                                                if v_isSharedCheck_2113_ == 0 {
                                                    v___x_2108_ = v___x_2095_;
                                                    v_isShared_2109_ = v_isSharedCheck_2113_;
                                                    state = 19;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2106_);
                                                    crate::leanh::lean_dec(v___x_2095_);
                                                    v___x_2108_ = crate::leanh::lean_box(0);
                                                    v_isShared_2109_ = v_isSharedCheck_2113_;
                                                    state = 19;
                                                    continue;
                                                }
                                            } else {
                                                v_a_2114_ =
                                                    crate::leanh::lean_ctor_get(v___x_2095_, 0);
                                                crate::leanh::lean_inc(v_a_2114_);
                                                crate::leanh::lean_dec_ref_known(v___x_2095_, 1);
                                                v___x_2115_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__7;
                                                v___x_2116_ = l_Lake_JsonObject_getJson_x3f(
                                                    v_val_2090_,
                                                    v___x_2115_,
                                                );
                                                crate::leanh::lean_dec(v_val_2090_);
                                                if crate::leanh::lean_obj_tag(v___x_2116_) == 0 {
                                                    crate::leanh::lean_dec(v_a_2114_);
                                                    v___x_2117_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0___closed__1;
                                                    return v___x_2117_;
                                                } else {
                                                    v_val_2118_ =
                                                        crate::leanh::lean_ctor_get(v___x_2116_, 0);
                                                    crate::leanh::lean_inc(v_val_2118_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2116_,
                                                        1,
                                                    );
                                                    v___x_2119_ =
                                                        l_Lean_Json_getStr_x3f(v_val_2118_);
                                                    if crate::leanh::lean_obj_tag(v___x_2119_) == 0
                                                    {
                                                        crate::leanh::lean_dec(v_a_2114_);
                                                        v_a_2120_ = crate::leanh::lean_ctor_get(
                                                            v___x_2119_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_2129_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_2119_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2129_ == 0 {
                                                            v___x_2122_ = v___x_2119_;
                                                            v_isShared_2123_ =
                                                                v_isSharedCheck_2129_;
                                                            state = 21;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_2120_);
                                                            crate::leanh::lean_dec(v___x_2119_);
                                                            v___x_2122_ = crate::leanh::lean_box(0);
                                                            v_isShared_2123_ =
                                                                v_isSharedCheck_2129_;
                                                            state = 21;
                                                            continue;
                                                        }
                                                    } else {
                                                        if crate::leanh::lean_obj_tag(v___x_2119_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec(v_a_2114_);
                                                            v_a_2130_ = crate::leanh::lean_ctor_get(
                                                                v___x_2119_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2137_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2119_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2137_ == 0 {
                                                                v___x_2132_ = v___x_2119_;
                                                                v_isShared_2133_ =
                                                                    v_isSharedCheck_2137_;
                                                                state = 23;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2130_);
                                                                crate::leanh::lean_dec(v___x_2119_);
                                                                v___x_2132_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2133_ =
                                                                    v_isSharedCheck_2137_;
                                                                state = 23;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_2138_ = crate::leanh::lean_ctor_get(
                                                                v___x_2119_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2146_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2119_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2146_ == 0 {
                                                                v___x_2140_ = v___x_2119_;
                                                                v_isShared_2141_ =
                                                                    v_isSharedCheck_2146_;
                                                                state = 25;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2138_);
                                                                crate::leanh::lean_dec(v___x_2119_);
                                                                v___x_2140_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2141_ =
                                                                    v_isSharedCheck_2146_;
                                                                state = 25;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2089_);
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2059_);
                    v___x_2147_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_2013_);
                    if crate::leanh::lean_obj_tag(v___x_2147_) == 0 {
                        v_a_2148_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                        v_isSharedCheck_2155_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2147_)) as u8;
                        if v_isSharedCheck_2155_ == 0 {
                            v___x_2150_ = v___x_2147_;
                            v_isShared_2151_ = v_isSharedCheck_2155_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2148_);
                            crate::leanh::lean_dec(v___x_2147_);
                            v___x_2150_ = crate::leanh::lean_box(0);
                            v_isShared_2151_ = v_isSharedCheck_2155_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v_a_2156_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                        v_isSharedCheck_2164_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2147_)) as u8;
                        if v_isSharedCheck_2164_ == 0 {
                            v___x_2158_ = v___x_2147_;
                            v_isShared_2159_ = v_isSharedCheck_2164_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2156_);
                            crate::leanh::lean_dec(v___x_2147_);
                            v___x_2158_ = crate::leanh::lean_box(0);
                            v_isShared_2159_ = v_isSharedCheck_2164_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2015_) == 1 {
                    crate::leanh::lean_dec(v_val_2013_);
                    v_val_2016_ = crate::leanh::lean_ctor_get(v_a_2015_, 0);
                    v_isSharedCheck_2040_ = (!crate::leanh::lean_is_exclusive(v_a_2015_)) as u8;
                    if v_isSharedCheck_2040_ == 0 {
                        v___x_2018_ = v_a_2015_;
                        v_isShared_2019_ = v_isSharedCheck_2040_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2016_);
                        crate::leanh::lean_dec(v_a_2015_);
                        v___x_2018_ = crate::leanh::lean_box(0);
                        v_isShared_2019_ = v_isSharedCheck_2040_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2015_);
                    v___x_2041_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_2013_);
                    if crate::leanh::lean_obj_tag(v___x_2041_) == 0 {
                        v_a_2042_ = crate::leanh::lean_ctor_get(v___x_2041_, 0);
                        v_isSharedCheck_2049_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2041_)) as u8;
                        if v_isSharedCheck_2049_ == 0 {
                            v___x_2044_ = v___x_2041_;
                            v_isShared_2045_ = v_isSharedCheck_2049_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2042_);
                            crate::leanh::lean_dec(v___x_2041_);
                            v___x_2044_ = crate::leanh::lean_box(0);
                            v_isShared_2045_ = v_isSharedCheck_2049_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_2050_ = crate::leanh::lean_ctor_get(v___x_2041_, 0);
                        v_isSharedCheck_2058_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2041_)) as u8;
                        if v_isSharedCheck_2058_ == 0 {
                            v___x_2052_ = v___x_2041_;
                            v_isShared_2053_ = v_isSharedCheck_2058_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2050_);
                            crate::leanh::lean_dec(v___x_2041_);
                            v___x_2052_ = crate::leanh::lean_box(0);
                            v_isShared_2053_ = v_isSharedCheck_2058_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_2020_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0_spec__0(v_val_2016_);
                if crate::leanh::lean_obj_tag(v___x_2020_) == 0 {
                    crate::leanh::lean_del_object(v___x_2018_);
                    v_a_2021_ = crate::leanh::lean_ctor_get(v___x_2020_, 0);
                    v_isSharedCheck_2028_ = (!crate::leanh::lean_is_exclusive(v___x_2020_)) as u8;
                    if v_isSharedCheck_2028_ == 0 {
                        v___x_2023_ = v___x_2020_;
                        v_isShared_2024_ = v_isSharedCheck_2028_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2021_);
                        crate::leanh::lean_dec(v___x_2020_);
                        v___x_2023_ = crate::leanh::lean_box(0);
                        v_isShared_2024_ = v_isSharedCheck_2028_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2029_ = crate::leanh::lean_ctor_get(v___x_2020_, 0);
                    v_isSharedCheck_2039_ = (!crate::leanh::lean_is_exclusive(v___x_2020_)) as u8;
                    if v_isSharedCheck_2039_ == 0 {
                        v___x_2031_ = v___x_2020_;
                        v_isShared_2032_ = v_isSharedCheck_2039_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2029_);
                        crate::leanh::lean_dec(v___x_2020_);
                        v___x_2031_ = crate::leanh::lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2039_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2024_ == 0 {
                    v___x_2026_ = v___x_2023_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
                    v___x_2026_ = v_reuseFailAlloc_2027_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2026_;
            }
            5 => {
                if v_isShared_2019_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2018_, 0);
                    crate::leanh::lean_ctor_set(v___x_2018_, 0, v_a_2029_);
                    v___x_2034_ = v___x_2018_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2029_);
                    v___x_2034_ = v_reuseFailAlloc_2038_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2032_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2031_, 0, v___x_2034_);
                    v___x_2036_ = v___x_2031_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2036_;
            }
            8 => {
                if v_isShared_2045_ == 0 {
                    v___x_2047_ = v___x_2044_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
                    v___x_2047_ = v_reuseFailAlloc_2048_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2047_;
            }
            10 => {
                v___x_2054_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2054_, 0, v_a_2050_);
                if v_isShared_2053_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2054_);
                    v___x_2056_ = v___x_2052_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2056_;
            }
            12 => {
                v___x_2062_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__0;
                v___x_2063_ = l_Lake_JsonObject_getJson_x3f(v_a_2060_, v___x_2062_);
                crate::leanh::lean_dec(v_a_2060_);
                if crate::leanh::lean_obj_tag(v___x_2063_) == 0 {
                    v_a_2015_ = v___x_2063_;
                    state = 1;
                    continue;
                } else {
                    v_val_2064_ = crate::leanh::lean_ctor_get(v___x_2063_, 0);
                    crate::leanh::lean_inc(v_val_2064_);
                    crate::leanh::lean_dec_ref_known(v___x_2063_, 1);
                    v___x_2065_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0_spec__0(v_val_2064_);
                    v_a_2066_ = crate::leanh::lean_ctor_get(v___x_2065_, 0);
                    crate::leanh::lean_inc(v_a_2066_);
                    crate::leanh::lean_dec_ref(v___x_2065_);
                    v_a_2015_ = v_a_2066_;
                    state = 1;
                    continue;
                }
            }
            13 => {
                v___x_2075_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__2;
                v___x_2076_ = lean_string_append(v___x_2075_, v_a_2071_);
                crate::leanh::lean_dec(v_a_2071_);
                if v_isShared_2074_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2073_, 0, v___x_2076_);
                    v___x_2078_ = v___x_2073_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
                    v___x_2078_ = v_reuseFailAlloc_2079_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2078_;
            }
            15 => {
                if v_isShared_2084_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2083_, 0);
                    v___x_2086_ = v___x_2083_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
                    v___x_2086_ = v_reuseFailAlloc_2087_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2086_;
            }
            17 => {
                v___x_2100_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__6;
                v___x_2101_ = lean_string_append(v___x_2100_, v_a_2096_);
                crate::leanh::lean_dec(v_a_2096_);
                if v_isShared_2099_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2098_, 0, v___x_2101_);
                    v___x_2103_ = v___x_2098_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2104_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
                    v___x_2103_ = v_reuseFailAlloc_2104_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2103_;
            }
            19 => {
                if v_isShared_2109_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2108_, 0);
                    v___x_2111_ = v___x_2108_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
                    v___x_2111_ = v_reuseFailAlloc_2112_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2111_;
            }
            21 => {
                v___x_2124_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkg_x3f_spec__0___closed__10;
                v___x_2125_ = lean_string_append(v___x_2124_, v_a_2120_);
                crate::leanh::lean_dec(v_a_2120_);
                if v_isShared_2123_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2122_, 0, v___x_2125_);
                    v___x_2127_ = v___x_2122_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2128_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
                    v___x_2127_ = v_reuseFailAlloc_2128_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2127_;
            }
            23 => {
                if v_isShared_2133_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2132_, 0);
                    v___x_2135_ = v___x_2132_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
                    v___x_2135_ = v_reuseFailAlloc_2136_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2135_;
            }
            25 => {
                v___x_2142_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2142_, 0, v_a_2114_);
                crate::leanh::lean_ctor_set(v___x_2142_, 1, v_a_2138_);
                if v_isShared_2141_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2140_, 0, v___x_2142_);
                    v___x_2144_ = v___x_2140_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
                    v___x_2144_ = v_reuseFailAlloc_2145_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2144_;
            }
            27 => {
                if v_isShared_2151_ == 0 {
                    v___x_2153_ = v___x_2150_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
                    v___x_2153_ = v_reuseFailAlloc_2154_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2153_;
            }
            29 => {
                v___x_2160_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2160_, 0, v_a_2156_);
                if v_isShared_2159_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2158_, 0, v___x_2160_);
                    v___x_2162_ = v___x_2158_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
                    v___x_2162_ = v_reuseFailAlloc_2163_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Reservoir_fetchPkgVersions(
    mut v_lakeEnv_2167_: *mut crate::leanh::LeanObject,
    mut v_owner_2168_: *mut crate::leanh::LeanObject,
    mut v_pkg_2169_: *mut crate::leanh::LeanObject,
    mut v_a_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_url_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: u8 = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u8 = 0;
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: u8 = 0;
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_status_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: u8 = 0;
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2257_: u8 = 0;
    let mut v_a_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: u8 = 0;
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2274_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_pkg_2169_);
                crate::leanh::lean_inc_ref(v_owner_2168_);
                v_url_2172_ =
                    l_Lake_Reservoir_pkgVersionsApiUrl(v_lakeEnv_2167_, v_owner_2168_, v_pkg_2169_);
                v___x_2173_ = l_Lake_Reservoir_lakeHeaders;
                v___x_2174_ = l_Lake_getUrl(v_url_2172_, v___x_2173_, v_a_2170_);
                if crate::leanh::lean_obj_tag(v___x_2174_) == 0 {
                    v_a_2175_ = crate::leanh::lean_ctor_get(v___x_2174_, 0);
                    v_a_2176_ = crate::leanh::lean_ctor_get(v___x_2174_, 1);
                    v_isSharedCheck_2257_ = (!crate::leanh::lean_is_exclusive(v___x_2174_)) as u8;
                    if v_isSharedCheck_2257_ == 0 {
                        v___x_2178_ = v___x_2174_;
                        v_isShared_2179_ = v_isSharedCheck_2257_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2176_);
                        crate::leanh::lean_inc(v_a_2175_);
                        crate::leanh::lean_dec(v___x_2174_);
                        v___x_2178_ = crate::leanh::lean_box(0);
                        v_isShared_2179_ = v_isSharedCheck_2257_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2258_ = crate::leanh::lean_ctor_get(v___x_2174_, 0);
                    v_a_2259_ = crate::leanh::lean_ctor_get(v___x_2174_, 1);
                    v_isSharedCheck_2274_ = (!crate::leanh::lean_is_exclusive(v___x_2174_)) as u8;
                    if v_isSharedCheck_2274_ == 0 {
                        v___x_2261_ = v___x_2174_;
                        v_isShared_2262_ = v_isSharedCheck_2274_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2259_);
                        crate::leanh::lean_inc(v_a_2258_);
                        crate::leanh::lean_dec(v___x_2174_);
                        v___x_2261_ = crate::leanh::lean_box(0);
                        v_isShared_2262_ = v_isSharedCheck_2274_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2175_);
                v___x_2180_ = l_Lean_Json_parse(v_a_2175_);
                if crate::leanh::lean_obj_tag(v___x_2180_) == 0 {
                    v_a_2181_ = crate::leanh::lean_ctor_get(v___x_2180_, 0);
                    crate::leanh::lean_inc(v_a_2181_);
                    crate::leanh::lean_dec_ref_known(v___x_2180_, 1);
                    v___x_2182_ = l_Lake_Reservoir_pkgApiUrl___closed__1;
                    v___x_2183_ = lean_string_append(v_owner_2168_, v___x_2182_);
                    v___x_2184_ = lean_string_append(v___x_2183_, v_pkg_2169_);
                    crate::leanh::lean_dec_ref(v_pkg_2169_);
                    v___x_2185_ = l_Lake_Reservoir_fetchPkg_x3f___closed__0;
                    crate::leanh::lean_inc_ref(v___x_2184_);
                    v___x_2186_ = lean_string_append(v___x_2184_, v___x_2185_);
                    v___x_2187_ = lean_string_append(v___x_2186_, v_a_2181_);
                    crate::leanh::lean_dec(v_a_2181_);
                    v___x_2188_ = 3;
                    v___x_2189_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2189_, 0, v___x_2187_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2189_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2188_,
                    );
                    v___x_2190_ = lean_array_get_size(v_a_2176_);
                    v___x_2191_ = lean_array_push(v_a_2176_, v___x_2189_);
                    v___x_2192_ = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
                    v___x_2193_ = lean_string_append(v___x_2184_, v___x_2192_);
                    v___x_2194_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2195_ = lean_string_utf8_byte_size(v_a_2175_);
                    v___x_2196_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2196_, 0, v_a_2175_);
                    crate::leanh::lean_ctor_set(v___x_2196_, 1, v___x_2194_);
                    crate::leanh::lean_ctor_set(v___x_2196_, 2, v___x_2195_);
                    v___x_2197_ = l_String_Slice_trimAscii(v___x_2196_);
                    v___x_2198_ = l_String_Slice_toString(v___x_2197_);
                    crate::leanh::lean_dec_ref(v___x_2197_);
                    v___x_2199_ = lean_string_append(v___x_2193_, v___x_2198_);
                    crate::leanh::lean_dec_ref(v___x_2198_);
                    v___x_2200_ = 0;
                    v___x_2201_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2201_, 0, v___x_2199_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2201_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2200_,
                    );
                    v___x_2202_ = lean_array_push(v___x_2191_, v___x_2201_);
                    if v_isShared_2179_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2178_, 1);
                        crate::leanh::lean_ctor_set(v___x_2178_, 1, v___x_2202_);
                        crate::leanh::lean_ctor_set(v___x_2178_, 0, v___x_2190_);
                        v___x_2204_ = v___x_2178_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2205_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2190_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2202_);
                        v___x_2204_ = v_reuseFailAlloc_2205_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2206_ = crate::leanh::lean_ctor_get(v___x_2180_, 0);
                    crate::leanh::lean_inc(v_a_2206_);
                    crate::leanh::lean_dec_ref_known(v___x_2180_, 1);
                    v___x_2207_ = l_Lake_ReservoirResp_fromJson_x3f___at___00Lake_Reservoir_fetchPkgVersions_spec__0(v_a_2206_);
                    if crate::leanh::lean_obj_tag(v___x_2207_) == 0 {
                        v_a_2208_ = crate::leanh::lean_ctor_get(v___x_2207_, 0);
                        crate::leanh::lean_inc(v_a_2208_);
                        crate::leanh::lean_dec_ref_known(v___x_2207_, 1);
                        v___x_2209_ = l_Lake_Reservoir_pkgApiUrl___closed__1;
                        v___x_2210_ = lean_string_append(v_owner_2168_, v___x_2209_);
                        v___x_2211_ = lean_string_append(v___x_2210_, v_pkg_2169_);
                        crate::leanh::lean_dec_ref(v_pkg_2169_);
                        v___x_2212_ = l_Lake_Reservoir_fetchPkg_x3f___closed__2;
                        crate::leanh::lean_inc_ref(v___x_2211_);
                        v___x_2213_ = lean_string_append(v___x_2211_, v___x_2212_);
                        v___x_2214_ = lean_string_append(v___x_2213_, v_a_2208_);
                        crate::leanh::lean_dec(v_a_2208_);
                        v___x_2215_ = 3;
                        v___x_2216_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2214_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2216_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2215_,
                        );
                        v___x_2217_ = lean_array_get_size(v_a_2176_);
                        v___x_2218_ = lean_array_push(v_a_2176_, v___x_2216_);
                        v___x_2219_ = l_Lake_Reservoir_fetchPkg_x3f___closed__1;
                        v___x_2220_ = lean_string_append(v___x_2211_, v___x_2219_);
                        v___x_2221_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2222_ = lean_string_utf8_byte_size(v_a_2175_);
                        v___x_2223_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2223_, 0, v_a_2175_);
                        crate::leanh::lean_ctor_set(v___x_2223_, 1, v___x_2221_);
                        crate::leanh::lean_ctor_set(v___x_2223_, 2, v___x_2222_);
                        v___x_2224_ = l_String_Slice_trimAscii(v___x_2223_);
                        v___x_2225_ = l_String_Slice_toString(v___x_2224_);
                        crate::leanh::lean_dec_ref(v___x_2224_);
                        v___x_2226_ = lean_string_append(v___x_2220_, v___x_2225_);
                        crate::leanh::lean_dec_ref(v___x_2225_);
                        v___x_2227_ = 0;
                        v___x_2228_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2228_, 0, v___x_2226_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2228_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2227_,
                        );
                        v___x_2229_ = lean_array_push(v___x_2218_, v___x_2228_);
                        if v_isShared_2179_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2178_, 1);
                            crate::leanh::lean_ctor_set(v___x_2178_, 1, v___x_2229_);
                            crate::leanh::lean_ctor_set(v___x_2178_, 0, v___x_2217_);
                            v___x_2231_ = v___x_2178_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2232_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2217_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 1, v___x_2229_);
                            v___x_2231_ = v_reuseFailAlloc_2232_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2175_);
                        v_a_2233_ = crate::leanh::lean_ctor_get(v___x_2207_, 0);
                        crate::leanh::lean_inc(v_a_2233_);
                        crate::leanh::lean_dec_ref_known(v___x_2207_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2233_) == 0 {
                            crate::leanh::lean_dec_ref(v_pkg_2169_);
                            crate::leanh::lean_dec_ref(v_owner_2168_);
                            v_a_2234_ = crate::leanh::lean_ctor_get(v_a_2233_, 0);
                            crate::leanh::lean_inc(v_a_2234_);
                            crate::leanh::lean_dec_ref_known(v_a_2233_, 1);
                            if v_isShared_2179_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2178_, 0, v_a_2234_);
                                v___x_2236_ = v___x_2178_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2237_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2234_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_a_2176_);
                                v___x_2236_ = v_reuseFailAlloc_2237_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_status_2238_ = crate::leanh::lean_ctor_get(v_a_2233_, 0);
                            crate::leanh::lean_inc(v_status_2238_);
                            v_message_2239_ = crate::leanh::lean_ctor_get(v_a_2233_, 1);
                            crate::leanh::lean_inc_ref(v_message_2239_);
                            crate::leanh::lean_dec_ref_known(v_a_2233_, 2);
                            v___x_2240_ = l_Lake_Reservoir_pkgApiUrl___closed__1;
                            v___x_2241_ = lean_string_append(v_owner_2168_, v___x_2240_);
                            v___x_2242_ = lean_string_append(v___x_2241_, v_pkg_2169_);
                            crate::leanh::lean_dec_ref(v_pkg_2169_);
                            v___x_2243_ = l_Lake_Reservoir_fetchPkgVersions___closed__0;
                            v___x_2244_ = lean_string_append(v___x_2242_, v___x_2243_);
                            v___x_2245_ = l_Nat_reprFast(v_status_2238_);
                            v___x_2246_ = lean_string_append(v___x_2244_, v___x_2245_);
                            crate::leanh::lean_dec_ref(v___x_2245_);
                            v___x_2247_ = l_Lake_Reservoir_fetchPkgVersions___closed__1;
                            v___x_2248_ = lean_string_append(v___x_2246_, v___x_2247_);
                            v___x_2249_ = lean_string_append(v___x_2248_, v_message_2239_);
                            crate::leanh::lean_dec_ref(v_message_2239_);
                            v___x_2250_ = 3;
                            v___x_2251_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_2251_, 0, v___x_2249_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_2251_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_2250_,
                            );
                            v___x_2252_ = lean_array_get_size(v_a_2176_);
                            v___x_2253_ = lean_array_push(v_a_2176_, v___x_2251_);
                            if v_isShared_2179_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2178_, 1);
                                crate::leanh::lean_ctor_set(v___x_2178_, 1, v___x_2253_);
                                crate::leanh::lean_ctor_set(v___x_2178_, 0, v___x_2252_);
                                v___x_2255_ = v___x_2178_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_2256_ =
                                    crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2252_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2256_, 1, v___x_2253_);
                                v___x_2255_ = v_reuseFailAlloc_2256_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_2204_;
            }
            3 => {
                return v___x_2231_;
            }
            4 => {
                return v___x_2236_;
            }
            5 => {
                return v___x_2255_;
            }
            6 => {
                v___x_2263_ = l_Lake_Reservoir_pkgApiUrl___closed__1;
                v___x_2264_ = lean_string_append(v_owner_2168_, v___x_2263_);
                v___x_2265_ = lean_string_append(v___x_2264_, v_pkg_2169_);
                crate::leanh::lean_dec_ref(v_pkg_2169_);
                v___x_2266_ = l_Lake_Reservoir_fetchPkg_x3f___closed__4;
                v___x_2267_ = lean_string_append(v___x_2265_, v___x_2266_);
                v___x_2268_ = 3;
                v___x_2269_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2269_, 0, v___x_2267_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2269_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2268_,
                );
                v___x_2270_ = lean_array_push(v_a_2259_, v___x_2269_);
                if v_isShared_2262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2261_, 1, v___x_2270_);
                    v___x_2272_ = v___x_2261_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2273_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2270_);
                    v___x_2272_ = v_reuseFailAlloc_2273_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2272_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Reservoir_fetchPkgVersions___boxed(
    mut v_lakeEnv_2275_: *mut crate::leanh::LeanObject,
    mut v_owner_2276_: *mut crate::leanh::LeanObject,
    mut v_pkg_2277_: *mut crate::leanh::LeanObject,
    mut v_a_2278_: *mut crate::leanh::LeanObject,
    mut v_a_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2280_ =
        l_Lake_Reservoir_fetchPkgVersions(v_lakeEnv_2275_, v_owner_2276_, v_pkg_2277_, v_a_2278_);
    return v_res_2280_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Reservoir(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Version(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Env(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Reservoir(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Url(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Reservoir(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Reservoir(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_JsonObject(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Version(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Env(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Reservoir(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Url(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Reservoir(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Reservoir(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Reservoir(builtin);
}

// Lean compiler output
// Module: Lake.Config.ConfigDecl
// Imports: Lake.Config.Opaque Lake.Config.LeanLibConfig Lake.Config.LeanExeConfig Lake.Config.ExternLibConfig Lake.Config.InputFileConfig Lake.Util.Name
use crate::ffi::{lean_array_push, lean_name_eq, lean_string_dec_eq};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Lake::Config::ExternLibConfig::{
    initialize_Lake_Config_ExternLibConfig, runtime_initialize_Lake_Config_ExternLibConfig,
};
use crate::r#gen::Lake::Config::InputFileConfig::{
    initialize_Lake_Config_InputFileConfig, runtime_initialize_Lake_Config_InputFileConfig,
};
use crate::r#gen::Lake::Config::Kinds::{l_Lake_ExternLib_keyword, l_Lake_LeanExe_keyword};
use crate::r#gen::Lake::Config::LeanExeConfig::{
    initialize_Lake_Config_LeanExeConfig, runtime_initialize_Lake_Config_LeanExeConfig,
};
use crate::r#gen::Lake::Config::LeanLibConfig::{
    initialize_Lake_Config_LeanLibConfig, runtime_initialize_Lake_Config_LeanLibConfig,
};
use crate::r#gen::Lake::Config::Opaque::{
    initialize_Lake_Config_Opaque, runtime_initialize_Lake_Config_Opaque,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
pub static l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 110, 102, 105, 103, 68, 101, 99, 108, 0]};
static mut l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject;
static l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject,11012187534809133843 as *mut crate::leanh::LeanObject] };
static mut l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameConfigDecl: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value:
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
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
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
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6_value:
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
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10_value)
            as *mut crate::leanh::LeanObject,
        3294379458557754569 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12_value:
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
    m_data: [114, 102, 108, 0],
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_PConfigDecl_pkg__eq___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_NConfigDecl_name__eq___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_KConfigDecl_kind__eq___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0_value:
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
    m_fun: l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0],
};
static mut l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 101, 120, 101, 0]};
static mut l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 120, 116, 101, 114, 110, 95, 108, 105, 98, 0]};
static mut l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 112, 117, 116, 95, 102, 105, 108, 101, 0]};
static mut l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 112, 117, 116, 95, 100, 105, 114, 0]};
static mut l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 76, 105, 98, 68, 101, 99, 108, 0],
};
static mut l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3963091058318347037 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameLeanLibDecl_unsafe__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameLeanLibDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 69, 120, 101, 68, 101, 99, 108, 0],
};
static mut l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2227531825659446058 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameLeanExeDecl_unsafe__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameLeanExeDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0_value:
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
        73, 110, 112, 117, 116, 70, 105, 108, 101, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16593811100477136826 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameInputFileDecl_unsafe__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameInputFileDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0_value:
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
    m_data: [73, 110, 112, 117, 116, 68, 105, 114, 68, 101, 99, 108, 0],
};
static mut l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10982118794685670592 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameInputDirDecl_unsafe__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameInputDirDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_468_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12;
    v___x_469_ = l_Lean_mkAtom(v___x_468_);
    return v___x_469_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_470_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13,
    );
    v___x_471_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5;
    v___x_472_ = lean_array_push(v___x_471_, v___x_470_);
    return v___x_472_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_473_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14,
    );
    v___x_474_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11;
    v___x_475_ = crate::leanh::lean_box(2);
    v___x_476_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_476_, 0, v___x_475_);
    crate::leanh::lean_ctor_set(v___x_476_, 1, v___x_474_);
    crate::leanh::lean_ctor_set(v___x_476_, 2, v___x_473_);
    return v___x_476_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_477_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15,
    );
    v___x_478_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5;
    v___x_479_ = lean_array_push(v___x_478_, v___x_477_);
    return v___x_479_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_480_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16,
    );
    v___x_481_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9;
    v___x_482_ = crate::leanh::lean_box(2);
    v___x_483_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_483_, 0, v___x_482_);
    crate::leanh::lean_ctor_set(v___x_483_, 1, v___x_481_);
    crate::leanh::lean_ctor_set(v___x_483_, 2, v___x_480_);
    return v___x_483_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_484_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17,
    );
    v___x_485_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5;
    v___x_486_ = lean_array_push(v___x_485_, v___x_484_);
    return v___x_486_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_487_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18,
    );
    v___x_488_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7;
    v___x_489_ = crate::leanh::lean_box(2);
    v___x_490_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_490_, 0, v___x_489_);
    crate::leanh::lean_ctor_set(v___x_490_, 1, v___x_488_);
    crate::leanh::lean_ctor_set(v___x_490_, 2, v___x_487_);
    return v___x_490_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_491_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19,
    );
    v___x_492_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5;
    v___x_493_ = lean_array_push(v___x_492_, v___x_491_);
    return v___x_493_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20,
    );
    v___x_495_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4;
    v___x_496_ = crate::leanh::lean_box(2);
    v___x_497_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_497_, 0, v___x_496_);
    crate::leanh::lean_ctor_set(v___x_497_, 1, v___x_495_);
    crate::leanh::lean_ctor_set(v___x_497_, 2, v___x_494_);
    return v___x_497_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam() -> *mut crate::leanh::LeanObject {
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21,
    );
    return v___x_498_;
}
pub unsafe fn _init_l_Lake_NConfigDecl_name__eq___autoParam() -> *mut crate::leanh::LeanObject {
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21,
    );
    return v___x_499_;
}
pub unsafe fn _init_l_Lake_KConfigDecl_kind__eq___autoParam() -> *mut crate::leanh::LeanObject {
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_500_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21,
    );
    return v___x_500_;
}
pub unsafe fn l_Lake_ConfigDecl_partialKey(
    mut v_self_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_502_ = crate::leanh::lean_ctor_get(v_self_501_, 1);
    v___x_503_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_name_502_);
    v___x_504_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_504_, 0, v___x_503_);
    crate::leanh::lean_ctor_set(v___x_504_, 1, v_name_502_);
    return v___x_504_;
}
pub unsafe fn l_Lake_ConfigDecl_partialKey___boxed(
    mut v_self_505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_506_ = l_Lake_ConfigDecl_partialKey(v_self_505_);
    crate::leanh::lean_dec_ref(v_self_505_);
    return v_res_506_;
}
pub unsafe fn l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0(
    mut v_x_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_508_ = crate::leanh::lean_ctor_get(v_x_507_, 1);
    v___x_509_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_name_508_);
    v___x_510_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_510_, 0, v___x_509_);
    crate::leanh::lean_ctor_set(v___x_510_, 1, v_name_508_);
    return v___x_510_;
}
pub unsafe fn l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0___boxed(
    mut v_x_511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_512_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0(v_x_511_);
    crate::leanh::lean_dec_ref(v_x_511_);
    return v_res_512_;
}
pub unsafe fn l_Lake_instCoeOutKConfigDeclPartialBuildKey(
    mut v_k_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_515_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0;
    return v___f_515_;
}
pub unsafe fn l_Lake_instCoeOutKConfigDeclPartialBuildKey___boxed(
    mut v_k_516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_517_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey(v_k_516_);
    crate::leanh::lean_dec(v_k_516_);
    return v_res_517_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x27___redArg(
    mut v_self_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_519_ = crate::leanh::lean_ctor_get(v_self_518_, 3);
    crate::leanh::lean_inc(v_config_519_);
    return v_config_519_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x27___redArg___boxed(
    mut v_self_520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_521_ = l_Lake_PConfigDecl_config_x27___redArg(v_self_520_);
    crate::leanh::lean_dec_ref(v_self_520_);
    return v_res_521_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x27(
    mut v_p_522_: *mut crate::leanh::LeanObject,
    mut v_self_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_524_ = crate::leanh::lean_ctor_get(v_self_523_, 3);
    crate::leanh::lean_inc(v_config_524_);
    return v_config_524_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x27___boxed(
    mut v_p_525_: *mut crate::leanh::LeanObject,
    mut v_self_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_527_ = l_Lake_PConfigDecl_config_x27(v_p_525_, v_self_526_);
    crate::leanh::lean_dec_ref(v_self_526_);
    crate::leanh::lean_dec(v_p_525_);
    return v_res_527_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x27___redArg(
    mut v_self_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_529_ = crate::leanh::lean_ctor_get(v_self_528_, 3);
    crate::leanh::lean_inc(v_config_529_);
    return v_config_529_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x27___redArg___boxed(
    mut v_self_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_531_ = l_Lake_NConfigDecl_config_x27___redArg(v_self_530_);
    crate::leanh::lean_dec_ref(v_self_530_);
    return v_res_531_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x27(
    mut v_p_532_: *mut crate::leanh::LeanObject,
    mut v_n_533_: *mut crate::leanh::LeanObject,
    mut v_self_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_535_ = crate::leanh::lean_ctor_get(v_self_534_, 3);
    crate::leanh::lean_inc(v_config_535_);
    return v_config_535_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x27___boxed(
    mut v_p_536_: *mut crate::leanh::LeanObject,
    mut v_n_537_: *mut crate::leanh::LeanObject,
    mut v_self_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_539_ = l_Lake_NConfigDecl_config_x27(v_p_536_, v_n_537_, v_self_538_);
    crate::leanh::lean_dec_ref(v_self_538_);
    crate::leanh::lean_dec(v_n_537_);
    crate::leanh::lean_dec(v_p_536_);
    return v_res_539_;
}
pub unsafe fn l_Lake_ConfigDecl_config_x3f(
    mut v_kind_540_: *mut crate::leanh::LeanObject,
    mut v_self_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: u8 = 0;
    v_kind_542_ = crate::leanh::lean_ctor_get(v_self_541_, 2);
    v_config_543_ = crate::leanh::lean_ctor_get(v_self_541_, 3);
    v___x_544_ = lean_name_eq(v_kind_542_, v_kind_540_);
    if v___x_544_ == 0 {
        let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_545_ = crate::leanh::lean_box(0);
        return v___x_545_;
    } else {
        let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_543_);
        v___x_546_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_546_, 0, v_config_543_);
        return v___x_546_;
    }
}
pub unsafe fn l_Lake_ConfigDecl_config_x3f___boxed(
    mut v_kind_547_: *mut crate::leanh::LeanObject,
    mut v_self_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_549_ = l_Lake_ConfigDecl_config_x3f(v_kind_547_, v_self_548_);
    crate::leanh::lean_dec_ref(v_self_548_);
    crate::leanh::lean_dec(v_kind_547_);
    return v_res_549_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x3f___redArg(
    mut v_kind_550_: *mut crate::leanh::LeanObject,
    mut v_self_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: u8 = 0;
    v_kind_552_ = crate::leanh::lean_ctor_get(v_self_551_, 2);
    v_config_553_ = crate::leanh::lean_ctor_get(v_self_551_, 3);
    v___x_554_ = lean_name_eq(v_kind_552_, v_kind_550_);
    if v___x_554_ == 0 {
        let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_555_ = crate::leanh::lean_box(0);
        return v___x_555_;
    } else {
        let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_553_);
        v___x_556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_556_, 0, v_config_553_);
        return v___x_556_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_config_x3f___redArg___boxed(
    mut v_kind_557_: *mut crate::leanh::LeanObject,
    mut v_self_558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_559_ = l_Lake_PConfigDecl_config_x3f___redArg(v_kind_557_, v_self_558_);
    crate::leanh::lean_dec_ref(v_self_558_);
    crate::leanh::lean_dec(v_kind_557_);
    return v_res_559_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x3f(
    mut v_p_560_: *mut crate::leanh::LeanObject,
    mut v_kind_561_: *mut crate::leanh::LeanObject,
    mut v_self_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u8 = 0;
    v_kind_563_ = crate::leanh::lean_ctor_get(v_self_562_, 2);
    v_config_564_ = crate::leanh::lean_ctor_get(v_self_562_, 3);
    v___x_565_ = lean_name_eq(v_kind_563_, v_kind_561_);
    if v___x_565_ == 0 {
        let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_566_ = crate::leanh::lean_box(0);
        return v___x_566_;
    } else {
        let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_564_);
        v___x_567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_567_, 0, v_config_564_);
        return v___x_567_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_config_x3f___boxed(
    mut v_p_568_: *mut crate::leanh::LeanObject,
    mut v_kind_569_: *mut crate::leanh::LeanObject,
    mut v_self_570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_571_ = l_Lake_PConfigDecl_config_x3f(v_p_568_, v_kind_569_, v_self_570_);
    crate::leanh::lean_dec_ref(v_self_570_);
    crate::leanh::lean_dec(v_kind_569_);
    crate::leanh::lean_dec(v_p_568_);
    return v_res_571_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x3f___redArg(
    mut v_kind_572_: *mut crate::leanh::LeanObject,
    mut v_self_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    v_kind_574_ = crate::leanh::lean_ctor_get(v_self_573_, 2);
    v_config_575_ = crate::leanh::lean_ctor_get(v_self_573_, 3);
    v___x_576_ = lean_name_eq(v_kind_574_, v_kind_572_);
    if v___x_576_ == 0 {
        let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_577_ = crate::leanh::lean_box(0);
        return v___x_577_;
    } else {
        let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_575_);
        v___x_578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_578_, 0, v_config_575_);
        return v___x_578_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_config_x3f___redArg___boxed(
    mut v_kind_579_: *mut crate::leanh::LeanObject,
    mut v_self_580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_581_ = l_Lake_NConfigDecl_config_x3f___redArg(v_kind_579_, v_self_580_);
    crate::leanh::lean_dec_ref(v_self_580_);
    crate::leanh::lean_dec(v_kind_579_);
    return v_res_581_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x3f(
    mut v_p_582_: *mut crate::leanh::LeanObject,
    mut v_n_583_: *mut crate::leanh::LeanObject,
    mut v_kind_584_: *mut crate::leanh::LeanObject,
    mut v_self_585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    v_kind_586_ = crate::leanh::lean_ctor_get(v_self_585_, 2);
    v_config_587_ = crate::leanh::lean_ctor_get(v_self_585_, 3);
    v___x_588_ = lean_name_eq(v_kind_586_, v_kind_584_);
    if v___x_588_ == 0 {
        let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_589_ = crate::leanh::lean_box(0);
        return v___x_589_;
    } else {
        let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_587_);
        v___x_590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_590_, 0, v_config_587_);
        return v___x_590_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_config_x3f___boxed(
    mut v_p_591_: *mut crate::leanh::LeanObject,
    mut v_n_592_: *mut crate::leanh::LeanObject,
    mut v_kind_593_: *mut crate::leanh::LeanObject,
    mut v_self_594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_595_ = l_Lake_NConfigDecl_config_x3f(v_p_591_, v_n_592_, v_kind_593_, v_self_594_);
    crate::leanh::lean_dec_ref(v_self_594_);
    crate::leanh::lean_dec(v_kind_593_);
    crate::leanh::lean_dec(v_n_592_);
    crate::leanh::lean_dec(v_p_591_);
    return v_res_595_;
}
pub unsafe fn l_Lake_ConfigDecl_leanLibConfig_x3f(
    mut v_self_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: u8 = 0;
    v_kind_600_ = crate::leanh::lean_ctor_get(v_self_599_, 2);
    v_config_601_ = crate::leanh::lean_ctor_get(v_self_599_, 3);
    v___x_602_ = l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1;
    v___x_603_ = lean_name_eq(v_kind_600_, v___x_602_);
    if v___x_603_ == 0 {
        let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_604_ = crate::leanh::lean_box(0);
        return v___x_604_;
    } else {
        let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_601_);
        v___x_605_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_605_, 0, v_config_601_);
        return v___x_605_;
    }
}
pub unsafe fn l_Lake_ConfigDecl_leanLibConfig_x3f___boxed(
    mut v_self_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_607_ = l_Lake_ConfigDecl_leanLibConfig_x3f(v_self_606_);
    crate::leanh::lean_dec_ref(v_self_606_);
    return v_res_607_;
}
pub unsafe fn l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(
    mut v_self_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: u8 = 0;
    v_kind_609_ = crate::leanh::lean_ctor_get(v_self_608_, 2);
    v_config_610_ = crate::leanh::lean_ctor_get(v_self_608_, 3);
    v___x_611_ = l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1;
    v___x_612_ = lean_name_eq(v_kind_609_, v___x_611_);
    if v___x_612_ == 0 {
        let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_613_ = crate::leanh::lean_box(0);
        return v___x_613_;
    } else {
        let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_610_);
        v___x_614_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_614_, 0, v_config_610_);
        return v___x_614_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_leanLibConfig_x3f___redArg___boxed(
    mut v_self_615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_616_ = l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(v_self_615_);
    crate::leanh::lean_dec_ref(v_self_615_);
    return v_res_616_;
}
pub unsafe fn l_Lake_NConfigDecl_leanLibConfig_x3f(
    mut v_p_617_: *mut crate::leanh::LeanObject,
    mut v_n_618_: *mut crate::leanh::LeanObject,
    mut v_self_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: u8 = 0;
    v_kind_620_ = crate::leanh::lean_ctor_get(v_self_619_, 2);
    v_config_621_ = crate::leanh::lean_ctor_get(v_self_619_, 3);
    v___x_622_ = l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1;
    v___x_623_ = lean_name_eq(v_kind_620_, v___x_622_);
    if v___x_623_ == 0 {
        let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_624_ = crate::leanh::lean_box(0);
        return v___x_624_;
    } else {
        let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_621_);
        v___x_625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_625_, 0, v_config_621_);
        return v___x_625_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_leanLibConfig_x3f___boxed(
    mut v_p_626_: *mut crate::leanh::LeanObject,
    mut v_n_627_: *mut crate::leanh::LeanObject,
    mut v_self_628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Lake_NConfigDecl_leanLibConfig_x3f(v_p_626_, v_n_627_, v_self_628_);
    crate::leanh::lean_dec_ref(v_self_628_);
    crate::leanh::lean_dec(v_n_627_);
    crate::leanh::lean_dec(v_p_626_);
    return v_res_629_;
}
pub unsafe fn l_Lake_ConfigDecl_leanExeConfig_x3f(
    mut v_self_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    v_kind_631_ = crate::leanh::lean_ctor_get(v_self_630_, 2);
    v_config_632_ = crate::leanh::lean_ctor_get(v_self_630_, 3);
    v___x_633_ = l_Lake_LeanExe_keyword;
    v___x_634_ = lean_name_eq(v_kind_631_, v___x_633_);
    if v___x_634_ == 0 {
        let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_635_ = crate::leanh::lean_box(0);
        return v___x_635_;
    } else {
        let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_632_);
        v___x_636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_636_, 0, v_config_632_);
        return v___x_636_;
    }
}
pub unsafe fn l_Lake_ConfigDecl_leanExeConfig_x3f___boxed(
    mut v_self_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_638_ = l_Lake_ConfigDecl_leanExeConfig_x3f(v_self_637_);
    crate::leanh::lean_dec_ref(v_self_637_);
    return v_res_638_;
}
pub unsafe fn l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(
    mut v_self_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    v_kind_640_ = crate::leanh::lean_ctor_get(v_self_639_, 2);
    v_config_641_ = crate::leanh::lean_ctor_get(v_self_639_, 3);
    v___x_642_ = l_Lake_LeanExe_keyword;
    v___x_643_ = lean_name_eq(v_kind_640_, v___x_642_);
    if v___x_643_ == 0 {
        let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_644_ = crate::leanh::lean_box(0);
        return v___x_644_;
    } else {
        let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_641_);
        v___x_645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_645_, 0, v_config_641_);
        return v___x_645_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_leanExeConfig_x3f___redArg___boxed(
    mut v_self_646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_647_ = l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(v_self_646_);
    crate::leanh::lean_dec_ref(v_self_646_);
    return v_res_647_;
}
pub unsafe fn l_Lake_NConfigDecl_leanExeConfig_x3f(
    mut v_p_648_: *mut crate::leanh::LeanObject,
    mut v_n_649_: *mut crate::leanh::LeanObject,
    mut v_self_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: u8 = 0;
    v_kind_651_ = crate::leanh::lean_ctor_get(v_self_650_, 2);
    v_config_652_ = crate::leanh::lean_ctor_get(v_self_650_, 3);
    v___x_653_ = l_Lake_LeanExe_keyword;
    v___x_654_ = lean_name_eq(v_kind_651_, v___x_653_);
    if v___x_654_ == 0 {
        let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_655_ = crate::leanh::lean_box(0);
        return v___x_655_;
    } else {
        let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_652_);
        v___x_656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_656_, 0, v_config_652_);
        return v___x_656_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_leanExeConfig_x3f___boxed(
    mut v_p_657_: *mut crate::leanh::LeanObject,
    mut v_n_658_: *mut crate::leanh::LeanObject,
    mut v_self_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Lake_NConfigDecl_leanExeConfig_x3f(v_p_657_, v_n_658_, v_self_659_);
    crate::leanh::lean_dec_ref(v_self_659_);
    crate::leanh::lean_dec(v_n_658_);
    crate::leanh::lean_dec(v_p_657_);
    return v_res_660_;
}
pub unsafe fn l_Lake_PConfigDecl_externLibConfig_x3f___redArg(
    mut v_self_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: u8 = 0;
    v_kind_662_ = crate::leanh::lean_ctor_get(v_self_661_, 2);
    v_config_663_ = crate::leanh::lean_ctor_get(v_self_661_, 3);
    v___x_664_ = l_Lake_ExternLib_keyword;
    v___x_665_ = lean_name_eq(v_kind_662_, v___x_664_);
    if v___x_665_ == 0 {
        let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_666_ = crate::leanh::lean_box(0);
        return v___x_666_;
    } else {
        let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_663_);
        v___x_667_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_667_, 0, v_config_663_);
        return v___x_667_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_externLibConfig_x3f___redArg___boxed(
    mut v_self_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_669_ = l_Lake_PConfigDecl_externLibConfig_x3f___redArg(v_self_668_);
    crate::leanh::lean_dec_ref(v_self_668_);
    return v_res_669_;
}
pub unsafe fn l_Lake_PConfigDecl_externLibConfig_x3f(
    mut v_p_670_: *mut crate::leanh::LeanObject,
    mut v_self_671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: u8 = 0;
    v_kind_672_ = crate::leanh::lean_ctor_get(v_self_671_, 2);
    v_config_673_ = crate::leanh::lean_ctor_get(v_self_671_, 3);
    v___x_674_ = l_Lake_ExternLib_keyword;
    v___x_675_ = lean_name_eq(v_kind_672_, v___x_674_);
    if v___x_675_ == 0 {
        let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_676_ = crate::leanh::lean_box(0);
        return v___x_676_;
    } else {
        let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_673_);
        v___x_677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_677_, 0, v_config_673_);
        return v___x_677_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_externLibConfig_x3f___boxed(
    mut v_p_678_: *mut crate::leanh::LeanObject,
    mut v_self_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_680_ = l_Lake_PConfigDecl_externLibConfig_x3f(v_p_678_, v_self_679_);
    crate::leanh::lean_dec_ref(v_self_679_);
    crate::leanh::lean_dec(v_p_678_);
    return v_res_680_;
}
pub unsafe fn l_Lake_NConfigDecl_externLibConfig_x3f___redArg(
    mut v_self_681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    v_kind_682_ = crate::leanh::lean_ctor_get(v_self_681_, 2);
    v_config_683_ = crate::leanh::lean_ctor_get(v_self_681_, 3);
    v___x_684_ = l_Lake_ExternLib_keyword;
    v___x_685_ = lean_name_eq(v_kind_682_, v___x_684_);
    if v___x_685_ == 0 {
        let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_686_ = crate::leanh::lean_box(0);
        return v___x_686_;
    } else {
        let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_683_);
        v___x_687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_687_, 0, v_config_683_);
        return v___x_687_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_externLibConfig_x3f___redArg___boxed(
    mut v_self_688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_689_ = l_Lake_NConfigDecl_externLibConfig_x3f___redArg(v_self_688_);
    crate::leanh::lean_dec_ref(v_self_688_);
    return v_res_689_;
}
pub unsafe fn l_Lake_NConfigDecl_externLibConfig_x3f(
    mut v_p_690_: *mut crate::leanh::LeanObject,
    mut v_n_691_: *mut crate::leanh::LeanObject,
    mut v_self_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: u8 = 0;
    v_kind_693_ = crate::leanh::lean_ctor_get(v_self_692_, 2);
    v_config_694_ = crate::leanh::lean_ctor_get(v_self_692_, 3);
    v___x_695_ = l_Lake_ExternLib_keyword;
    v___x_696_ = lean_name_eq(v_kind_693_, v___x_695_);
    if v___x_696_ == 0 {
        let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_697_ = crate::leanh::lean_box(0);
        return v___x_697_;
    } else {
        let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_694_);
        v___x_698_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_698_, 0, v_config_694_);
        return v___x_698_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_externLibConfig_x3f___boxed(
    mut v_p_699_: *mut crate::leanh::LeanObject,
    mut v_n_700_: *mut crate::leanh::LeanObject,
    mut v_self_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_702_ = l_Lake_NConfigDecl_externLibConfig_x3f(v_p_699_, v_n_700_, v_self_701_);
    crate::leanh::lean_dec_ref(v_self_701_);
    crate::leanh::lean_dec(v_n_700_);
    crate::leanh::lean_dec(v_p_699_);
    return v_res_702_;
}
pub unsafe fn l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg(
    mut v_kind_708_: *mut crate::leanh::LeanObject,
    mut v_h__1_709_: *mut crate::leanh::LeanObject,
    mut v_h__2_710_: *mut crate::leanh::LeanObject,
    mut v_h__3_711_: *mut crate::leanh::LeanObject,
    mut v_h__4_712_: *mut crate::leanh::LeanObject,
    mut v_h__5_713_: *mut crate::leanh::LeanObject,
    mut v_h__6_714_: *mut crate::leanh::LeanObject,
    mut v_h__7_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_kind_708_) {
        1 => {
            let mut v_pre_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_712_);
            v_pre_716_ = crate::leanh::lean_ctor_get(v_kind_708_, 0);
            if crate::leanh::lean_obj_tag(v_pre_716_) == 0 {
                let mut v_str_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_719_: u8 = 0;
                v_str_717_ = crate::leanh::lean_ctor_get(v_kind_708_, 1);
                v___x_718_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0;
                v___x_719_ = lean_string_dec_eq(v_str_717_, v___x_718_);
                if v___x_719_ == 0 {
                    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_721_: u8 = 0;
                    crate::leanh::lean_dec(v_h__1_709_);
                    v___x_720_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1;
                    v___x_721_ = lean_string_dec_eq(v_str_717_, v___x_720_);
                    if v___x_721_ == 0 {
                        let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_723_: u8 = 0;
                        crate::leanh::lean_dec(v_h__2_710_);
                        v___x_722_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2;
                        v___x_723_ = lean_string_dec_eq(v_str_717_, v___x_722_);
                        if v___x_723_ == 0 {
                            let mut v___x_724_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_725_: u8 = 0;
                            crate::leanh::lean_dec(v_h__3_711_);
                            v___x_724_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3;
                            v___x_725_ = lean_string_dec_eq(v_str_717_, v___x_724_);
                            if v___x_725_ == 0 {
                                let mut v___x_726_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_727_: u8 = 0;
                                crate::leanh::lean_dec(v_h__5_713_);
                                v___x_726_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4;
                                v___x_727_ = lean_string_dec_eq(v_str_717_, v___x_726_);
                                if v___x_727_ == 0 {
                                    let mut v___x_728_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec(v_h__6_714_);
                                    v___x_728_ = crate::leanh::lean_apply_7(
                                        v_h__7_715_,
                                        v_kind_708_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                    );
                                    return v___x_728_;
                                } else {
                                    let mut v___x_729_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_730_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec_ref_known(v_kind_708_, 2);
                                    crate::leanh::lean_dec(v_h__7_715_);
                                    v___x_729_ = crate::leanh::lean_box(0);
                                    v___x_730_ =
                                        crate::leanh::lean_apply_1(v_h__6_714_, v___x_729_);
                                    return v___x_730_;
                                }
                            } else {
                                let mut v___x_731_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_732_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                crate::leanh::lean_dec_ref_known(v_kind_708_, 2);
                                crate::leanh::lean_dec(v_h__7_715_);
                                crate::leanh::lean_dec(v_h__6_714_);
                                v___x_731_ = crate::leanh::lean_box(0);
                                v___x_732_ = crate::leanh::lean_apply_1(v_h__5_713_, v___x_731_);
                                return v___x_732_;
                            }
                        } else {
                            let mut v___x_733_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_734_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref_known(v_kind_708_, 2);
                            crate::leanh::lean_dec(v_h__7_715_);
                            crate::leanh::lean_dec(v_h__6_714_);
                            crate::leanh::lean_dec(v_h__5_713_);
                            v___x_733_ = crate::leanh::lean_box(0);
                            v___x_734_ = crate::leanh::lean_apply_1(v_h__3_711_, v___x_733_);
                            return v___x_734_;
                        }
                    } else {
                        let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v_kind_708_, 2);
                        crate::leanh::lean_dec(v_h__7_715_);
                        crate::leanh::lean_dec(v_h__6_714_);
                        crate::leanh::lean_dec(v_h__5_713_);
                        crate::leanh::lean_dec(v_h__3_711_);
                        v___x_735_ = crate::leanh::lean_box(0);
                        v___x_736_ = crate::leanh::lean_apply_1(v_h__2_710_, v___x_735_);
                        return v___x_736_;
                    }
                } else {
                    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v_kind_708_, 2);
                    crate::leanh::lean_dec(v_h__7_715_);
                    crate::leanh::lean_dec(v_h__6_714_);
                    crate::leanh::lean_dec(v_h__5_713_);
                    crate::leanh::lean_dec(v_h__3_711_);
                    crate::leanh::lean_dec(v_h__2_710_);
                    v___x_737_ = crate::leanh::lean_box(0);
                    v___x_738_ = crate::leanh::lean_apply_1(v_h__1_709_, v___x_737_);
                    return v___x_738_;
                }
            } else {
                let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__6_714_);
                crate::leanh::lean_dec(v_h__5_713_);
                crate::leanh::lean_dec(v_h__3_711_);
                crate::leanh::lean_dec(v_h__2_710_);
                crate::leanh::lean_dec(v_h__1_709_);
                v___x_739_ = crate::leanh::lean_apply_7(
                    v_h__7_715_,
                    v_kind_708_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_739_;
            }
        }
        0 => {
            let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_715_);
            crate::leanh::lean_dec(v_h__6_714_);
            crate::leanh::lean_dec(v_h__5_713_);
            crate::leanh::lean_dec(v_h__3_711_);
            crate::leanh::lean_dec(v_h__2_710_);
            crate::leanh::lean_dec(v_h__1_709_);
            v___x_740_ = crate::leanh::lean_box(0);
            v___x_741_ = crate::leanh::lean_apply_1(v_h__4_712_, v___x_740_);
            return v___x_741_;
        }
        _ => {
            let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_714_);
            crate::leanh::lean_dec(v_h__5_713_);
            crate::leanh::lean_dec(v_h__4_712_);
            crate::leanh::lean_dec(v_h__3_711_);
            crate::leanh::lean_dec(v_h__2_710_);
            crate::leanh::lean_dec(v_h__1_709_);
            v___x_742_ = crate::leanh::lean_apply_7(
                v_h__7_715_,
                v_kind_708_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_742_;
        }
    }
}
pub unsafe fn l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter(
    mut v_motive_743_: *mut crate::leanh::LeanObject,
    mut v_kind_744_: *mut crate::leanh::LeanObject,
    mut v_h__1_745_: *mut crate::leanh::LeanObject,
    mut v_h__2_746_: *mut crate::leanh::LeanObject,
    mut v_h__3_747_: *mut crate::leanh::LeanObject,
    mut v_h__4_748_: *mut crate::leanh::LeanObject,
    mut v_h__5_749_: *mut crate::leanh::LeanObject,
    mut v_h__6_750_: *mut crate::leanh::LeanObject,
    mut v_h__7_751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_kind_744_) {
        1 => {
            let mut v_pre_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_748_);
            v_pre_752_ = crate::leanh::lean_ctor_get(v_kind_744_, 0);
            if crate::leanh::lean_obj_tag(v_pre_752_) == 0 {
                let mut v_str_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_755_: u8 = 0;
                v_str_753_ = crate::leanh::lean_ctor_get(v_kind_744_, 1);
                v___x_754_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0;
                v___x_755_ = lean_string_dec_eq(v_str_753_, v___x_754_);
                if v___x_755_ == 0 {
                    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_757_: u8 = 0;
                    crate::leanh::lean_dec(v_h__1_745_);
                    v___x_756_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1;
                    v___x_757_ = lean_string_dec_eq(v_str_753_, v___x_756_);
                    if v___x_757_ == 0 {
                        let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_759_: u8 = 0;
                        crate::leanh::lean_dec(v_h__2_746_);
                        v___x_758_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2;
                        v___x_759_ = lean_string_dec_eq(v_str_753_, v___x_758_);
                        if v___x_759_ == 0 {
                            let mut v___x_760_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_761_: u8 = 0;
                            crate::leanh::lean_dec(v_h__3_747_);
                            v___x_760_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3;
                            v___x_761_ = lean_string_dec_eq(v_str_753_, v___x_760_);
                            if v___x_761_ == 0 {
                                let mut v___x_762_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_763_: u8 = 0;
                                crate::leanh::lean_dec(v_h__5_749_);
                                v___x_762_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4;
                                v___x_763_ = lean_string_dec_eq(v_str_753_, v___x_762_);
                                if v___x_763_ == 0 {
                                    let mut v___x_764_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec(v_h__6_750_);
                                    v___x_764_ = crate::leanh::lean_apply_7(
                                        v_h__7_751_,
                                        v_kind_744_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                    );
                                    return v___x_764_;
                                } else {
                                    let mut v___x_765_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_766_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec_ref_known(v_kind_744_, 2);
                                    crate::leanh::lean_dec(v_h__7_751_);
                                    v___x_765_ = crate::leanh::lean_box(0);
                                    v___x_766_ =
                                        crate::leanh::lean_apply_1(v_h__6_750_, v___x_765_);
                                    return v___x_766_;
                                }
                            } else {
                                let mut v___x_767_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_768_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                crate::leanh::lean_dec_ref_known(v_kind_744_, 2);
                                crate::leanh::lean_dec(v_h__7_751_);
                                crate::leanh::lean_dec(v_h__6_750_);
                                v___x_767_ = crate::leanh::lean_box(0);
                                v___x_768_ = crate::leanh::lean_apply_1(v_h__5_749_, v___x_767_);
                                return v___x_768_;
                            }
                        } else {
                            let mut v___x_769_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_770_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref_known(v_kind_744_, 2);
                            crate::leanh::lean_dec(v_h__7_751_);
                            crate::leanh::lean_dec(v_h__6_750_);
                            crate::leanh::lean_dec(v_h__5_749_);
                            v___x_769_ = crate::leanh::lean_box(0);
                            v___x_770_ = crate::leanh::lean_apply_1(v_h__3_747_, v___x_769_);
                            return v___x_770_;
                        }
                    } else {
                        let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v_kind_744_, 2);
                        crate::leanh::lean_dec(v_h__7_751_);
                        crate::leanh::lean_dec(v_h__6_750_);
                        crate::leanh::lean_dec(v_h__5_749_);
                        crate::leanh::lean_dec(v_h__3_747_);
                        v___x_771_ = crate::leanh::lean_box(0);
                        v___x_772_ = crate::leanh::lean_apply_1(v_h__2_746_, v___x_771_);
                        return v___x_772_;
                    }
                } else {
                    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v_kind_744_, 2);
                    crate::leanh::lean_dec(v_h__7_751_);
                    crate::leanh::lean_dec(v_h__6_750_);
                    crate::leanh::lean_dec(v_h__5_749_);
                    crate::leanh::lean_dec(v_h__3_747_);
                    crate::leanh::lean_dec(v_h__2_746_);
                    v___x_773_ = crate::leanh::lean_box(0);
                    v___x_774_ = crate::leanh::lean_apply_1(v_h__1_745_, v___x_773_);
                    return v___x_774_;
                }
            } else {
                let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__6_750_);
                crate::leanh::lean_dec(v_h__5_749_);
                crate::leanh::lean_dec(v_h__3_747_);
                crate::leanh::lean_dec(v_h__2_746_);
                crate::leanh::lean_dec(v_h__1_745_);
                v___x_775_ = crate::leanh::lean_apply_7(
                    v_h__7_751_,
                    v_kind_744_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_775_;
            }
        }
        0 => {
            let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_751_);
            crate::leanh::lean_dec(v_h__6_750_);
            crate::leanh::lean_dec(v_h__5_749_);
            crate::leanh::lean_dec(v_h__3_747_);
            crate::leanh::lean_dec(v_h__2_746_);
            crate::leanh::lean_dec(v_h__1_745_);
            v___x_776_ = crate::leanh::lean_box(0);
            v___x_777_ = crate::leanh::lean_apply_1(v_h__4_748_, v___x_776_);
            return v___x_777_;
        }
        _ => {
            let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_750_);
            crate::leanh::lean_dec(v_h__5_749_);
            crate::leanh::lean_dec(v_h__4_748_);
            crate::leanh::lean_dec(v_h__3_747_);
            crate::leanh::lean_dec(v_h__2_746_);
            crate::leanh::lean_dec(v_h__1_745_);
            v___x_778_ = crate::leanh::lean_apply_7(
                v_h__7_751_,
                v_kind_744_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_778_;
        }
    }
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig___redArg(
    mut v_self_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_780_ = crate::leanh::lean_ctor_get(v_self_779_, 3);
    crate::leanh::lean_inc(v_config_780_);
    return v_config_780_;
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig___redArg___boxed(
    mut v_self_781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_782_ = l_Lake_PConfigDecl_opaqueTargetConfig___redArg(v_self_781_);
    crate::leanh::lean_dec_ref(v_self_781_);
    return v_res_782_;
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig(
    mut v_p_783_: *mut crate::leanh::LeanObject,
    mut v_self_784_: *mut crate::leanh::LeanObject,
    mut v_h_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_786_ = crate::leanh::lean_ctor_get(v_self_784_, 3);
    crate::leanh::lean_inc(v_config_786_);
    return v_config_786_;
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig___boxed(
    mut v_p_787_: *mut crate::leanh::LeanObject,
    mut v_self_788_: *mut crate::leanh::LeanObject,
    mut v_h_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Lake_PConfigDecl_opaqueTargetConfig(v_p_787_, v_self_788_, v_h_789_);
    crate::leanh::lean_dec_ref(v_self_788_);
    crate::leanh::lean_dec(v_p_787_);
    return v_res_790_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig___redArg(
    mut v_self_791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_792_ = crate::leanh::lean_ctor_get(v_self_791_, 3);
    crate::leanh::lean_inc(v_config_792_);
    return v_config_792_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig___redArg___boxed(
    mut v_self_793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_794_ = l_Lake_NConfigDecl_opaqueTargetConfig___redArg(v_self_793_);
    crate::leanh::lean_dec_ref(v_self_793_);
    return v_res_794_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig(
    mut v_p_795_: *mut crate::leanh::LeanObject,
    mut v_n_796_: *mut crate::leanh::LeanObject,
    mut v_self_797_: *mut crate::leanh::LeanObject,
    mut v_h_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_799_ = crate::leanh::lean_ctor_get(v_self_797_, 3);
    crate::leanh::lean_inc(v_config_799_);
    return v_config_799_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig___boxed(
    mut v_p_800_: *mut crate::leanh::LeanObject,
    mut v_n_801_: *mut crate::leanh::LeanObject,
    mut v_self_802_: *mut crate::leanh::LeanObject,
    mut v_h_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Lake_NConfigDecl_opaqueTargetConfig(v_p_800_, v_n_801_, v_self_802_, v_h_803_);
    crate::leanh::lean_dec_ref(v_self_802_);
    crate::leanh::lean_dec(v_n_801_);
    crate::leanh::lean_dec(v_p_800_);
    return v_res_804_;
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(
    mut v_self_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: u8 = 0;
    v_kind_806_ = crate::leanh::lean_ctor_get(v_self_805_, 2);
    v_config_807_ = crate::leanh::lean_ctor_get(v_self_805_, 3);
    v___x_808_ = l_Lean_Name_isAnonymous(v_kind_806_);
    if v___x_808_ == 0 {
        let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_809_ = crate::leanh::lean_box(0);
        return v___x_809_;
    } else {
        let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_807_);
        v___x_810_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_810_, 0, v_config_807_);
        return v___x_810_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(
    mut v_self_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(v_self_811_);
    crate::leanh::lean_dec_ref(v_self_811_);
    return v_res_812_;
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig_x3f(
    mut v_p_813_: *mut crate::leanh::LeanObject,
    mut v_self_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: u8 = 0;
    v_kind_815_ = crate::leanh::lean_ctor_get(v_self_814_, 2);
    v_config_816_ = crate::leanh::lean_ctor_get(v_self_814_, 3);
    v___x_817_ = l_Lean_Name_isAnonymous(v_kind_815_);
    if v___x_817_ == 0 {
        let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_818_ = crate::leanh::lean_box(0);
        return v___x_818_;
    } else {
        let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_816_);
        v___x_819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_819_, 0, v_config_816_);
        return v___x_819_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig_x3f___boxed(
    mut v_p_820_: *mut crate::leanh::LeanObject,
    mut v_self_821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_822_ = l_Lake_PConfigDecl_opaqueTargetConfig_x3f(v_p_820_, v_self_821_);
    crate::leanh::lean_dec_ref(v_self_821_);
    crate::leanh::lean_dec(v_p_820_);
    return v_res_822_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(
    mut v_self_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: u8 = 0;
    v_kind_824_ = crate::leanh::lean_ctor_get(v_self_823_, 2);
    v_config_825_ = crate::leanh::lean_ctor_get(v_self_823_, 3);
    v___x_826_ = l_Lean_Name_isAnonymous(v_kind_824_);
    if v___x_826_ == 0 {
        let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_827_ = crate::leanh::lean_box(0);
        return v___x_827_;
    } else {
        let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_825_);
        v___x_828_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_828_, 0, v_config_825_);
        return v___x_828_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(
    mut v_self_829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_830_ = l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(v_self_829_);
    crate::leanh::lean_dec_ref(v_self_829_);
    return v_res_830_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig_x3f(
    mut v_p_831_: *mut crate::leanh::LeanObject,
    mut v_n_832_: *mut crate::leanh::LeanObject,
    mut v_self_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: u8 = 0;
    v_kind_834_ = crate::leanh::lean_ctor_get(v_self_833_, 2);
    v_config_835_ = crate::leanh::lean_ctor_get(v_self_833_, 3);
    v___x_836_ = l_Lean_Name_isAnonymous(v_kind_834_);
    if v___x_836_ == 0 {
        let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_837_ = crate::leanh::lean_box(0);
        return v___x_837_;
    } else {
        let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_config_835_);
        v___x_838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_838_, 0, v_config_835_);
        return v___x_838_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig_x3f___boxed(
    mut v_p_839_: *mut crate::leanh::LeanObject,
    mut v_n_840_: *mut crate::leanh::LeanObject,
    mut v_self_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_842_ = l_Lake_NConfigDecl_opaqueTargetConfig_x3f(v_p_839_, v_n_840_, v_self_841_);
    crate::leanh::lean_dec_ref(v_self_841_);
    crate::leanh::lean_dec(v_n_840_);
    crate::leanh::lean_dec(v_p_839_);
    return v_res_842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_ConfigDecl(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Opaque(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanLibConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExeConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLibConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFileConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_ConfigDecl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lake_PConfigDecl_pkg__eq___autoParam = _init_l_Lake_PConfigDecl_pkg__eq___autoParam();
    crate::leanh::lean_mark_persistent(l_Lake_PConfigDecl_pkg__eq___autoParam);
    l_Lake_NConfigDecl_name__eq___autoParam = _init_l_Lake_NConfigDecl_name__eq___autoParam();
    crate::leanh::lean_mark_persistent(l_Lake_NConfigDecl_name__eq___autoParam);
    l_Lake_KConfigDecl_kind__eq___autoParam = _init_l_Lake_KConfigDecl_kind__eq___autoParam();
    crate::leanh::lean_mark_persistent(l_Lake_KConfigDecl_kind__eq___autoParam);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_ConfigDecl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Opaque(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LeanLibConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LeanExeConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_ExternLibConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_InputFileConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ConfigDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_ConfigDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_ConfigDecl(builtin);
}

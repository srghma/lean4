// Lean compiler output
// Module: Lake.Config.ConfigDecl
// Imports: Lake.Config.Opaque Lake.Config.LeanLibConfig Lake.Config.LeanExeConfig Lake.Config.ExternLibConfig Lake.Config.InputFileConfig Lake.Util.Name
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_mkAtom,
};
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_string_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_7, lean_box,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_obj_tag,
};
pub static l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_: *mut LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject;
pub static l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 110, 102, 105, 103, 68, 101, 99, 108, 0]};
static mut l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_: *mut LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject;
static l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject,11012187534809133843 as *mut LeanObject] };
static mut l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_: *mut LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject;
pub static mut l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_: *mut LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject;
pub static mut l_Lake_instTypeNameConfigDecl: *mut LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value: LeanStringObject<5> =
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
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3_value)
        as *mut LeanObject;
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6_value: LeanStringObject<19> =
    LeanStringObject {
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
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6_value)
        as *mut LeanObject;
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value)
        as *mut LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10_value)
        as *mut LeanObject;
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10_value)
                as *mut LeanObject,
            3294379458557754569 as *mut LeanObject,
        ],
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value)
        as *mut LeanObject;
pub static l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12_value: LeanStringObject<4> =
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
        m_data: [114, 102, 108, 0],
    };
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12_value)
        as *mut LeanObject;
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_PConfigDecl_pkg__eq___autoParam: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_NConfigDecl_name__eq___autoParam: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_KConfigDecl_kind__eq___autoParam: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0_value)
                as *mut LeanObject,
            12295998048739818339 as *mut LeanObject,
        ],
    };
static mut l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 101, 120, 101, 0]};
static mut l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 120, 116, 101, 114, 110, 95, 108, 105, 98, 0]};
static mut l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 112, 117, 116, 95, 102, 105, 108, 101, 0]};
static mut l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 112, 117, 116, 95, 100, 105, 114, 0]};
static mut l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0_value)
        as *mut LeanObject;
static l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0_value)
                as *mut LeanObject,
            3963091058318347037 as *mut LeanObject,
        ],
    };
static mut l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instTypeNameLeanLibDecl_unsafe__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instTypeNameLeanLibDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0_value)
        as *mut LeanObject;
static l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0_value)
                as *mut LeanObject,
            2227531825659446058 as *mut LeanObject,
        ],
    };
static mut l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instTypeNameLeanExeDecl_unsafe__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instTypeNameLeanExeDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0_value: LeanStringObject<14> =
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
            73, 110, 112, 117, 116, 70, 105, 108, 101, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0_value)
        as *mut LeanObject;
static l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0_value)
                as *mut LeanObject,
            16593811100477136826 as *mut LeanObject,
        ],
    };
static mut l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instTypeNameInputFileDecl_unsafe__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instTypeNameInputFileDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0_value: LeanStringObject<13> =
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
        m_data: [73, 110, 112, 117, 116, 68, 105, 114, 68, 101, 99, 108, 0],
    };
static mut l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0_value)
        as *mut LeanObject;
static l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0_value)
                as *mut LeanObject,
            10982118794685670592 as *mut LeanObject,
        ],
    };
static mut l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instTypeNameInputDirDecl_unsafe__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instTypeNameInputDirDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13() -> *mut LeanObject {
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    v___x_468_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12;
    v___x_469_ = l_Lean_mkAtom(v___x_468_);
    return v___x_469_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14() -> *mut LeanObject {
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    v___x_470_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13,
    );
    v___x_471_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5;
    v___x_472_ = lean_array_push(v___x_471_, v___x_470_);
    return v___x_472_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15() -> *mut LeanObject {
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    v___x_473_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14,
    );
    v___x_474_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11;
    v___x_475_ = lean_box(2);
    v___x_476_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_476_, 0, v___x_475_);
    lean_ctor_set(v___x_476_, 1, v___x_474_);
    lean_ctor_set(v___x_476_, 2, v___x_473_);
    return v___x_476_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16() -> *mut LeanObject {
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    v___x_477_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15,
    );
    v___x_478_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5;
    v___x_479_ = lean_array_push(v___x_478_, v___x_477_);
    return v___x_479_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17() -> *mut LeanObject {
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    v___x_480_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16,
    );
    v___x_481_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9;
    v___x_482_ = lean_box(2);
    v___x_483_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_483_, 0, v___x_482_);
    lean_ctor_set(v___x_483_, 1, v___x_481_);
    lean_ctor_set(v___x_483_, 2, v___x_480_);
    return v___x_483_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18() -> *mut LeanObject {
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v___x_484_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17,
    );
    v___x_485_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5;
    v___x_486_ = lean_array_push(v___x_485_, v___x_484_);
    return v___x_486_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19() -> *mut LeanObject {
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    v___x_487_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18,
    );
    v___x_488_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7;
    v___x_489_ = lean_box(2);
    v___x_490_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_490_, 0, v___x_489_);
    lean_ctor_set(v___x_490_, 1, v___x_488_);
    lean_ctor_set(v___x_490_, 2, v___x_487_);
    return v___x_490_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20() -> *mut LeanObject {
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    v___x_491_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19,
    );
    v___x_492_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5;
    v___x_493_ = lean_array_push(v___x_492_, v___x_491_);
    return v___x_493_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21() -> *mut LeanObject {
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    v___x_494_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20,
    );
    v___x_495_ = l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4;
    v___x_496_ = lean_box(2);
    v___x_497_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_497_, 0, v___x_496_);
    lean_ctor_set(v___x_497_, 1, v___x_495_);
    lean_ctor_set(v___x_497_, 2, v___x_494_);
    return v___x_497_;
}
pub unsafe fn _init_l_Lake_PConfigDecl_pkg__eq___autoParam() -> *mut LeanObject {
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    v___x_498_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21,
    );
    return v___x_498_;
}
pub unsafe fn _init_l_Lake_NConfigDecl_name__eq___autoParam() -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21,
    );
    return v___x_499_;
}
pub unsafe fn _init_l_Lake_KConfigDecl_kind__eq___autoParam() -> *mut LeanObject {
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    v___x_500_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once),
        _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21,
    );
    return v___x_500_;
}
pub unsafe fn l_Lake_ConfigDecl_partialKey(mut v_self_501_: *mut LeanObject) -> *mut LeanObject {
    let mut v_name_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    v_name_502_ = lean_ctor_get(v_self_501_, 1);
    v___x_503_ = lean_box(0);
    lean_inc(v_name_502_);
    v___x_504_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_504_, 0, v___x_503_);
    lean_ctor_set(v___x_504_, 1, v_name_502_);
    return v___x_504_;
}
pub unsafe fn l_Lake_ConfigDecl_partialKey___boxed(
    mut v_self_505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_506_: *mut LeanObject = core::ptr::null_mut();
    v_res_506_ = l_Lake_ConfigDecl_partialKey(v_self_505_);
    lean_dec_ref(v_self_505_);
    return v_res_506_;
}
pub unsafe fn l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0(
    mut v_x_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    v_name_508_ = lean_ctor_get(v_x_507_, 1);
    v___x_509_ = lean_box(0);
    lean_inc(v_name_508_);
    v___x_510_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_510_, 0, v___x_509_);
    lean_ctor_set(v___x_510_, 1, v_name_508_);
    return v___x_510_;
}
pub unsafe fn l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0___boxed(
    mut v_x_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_512_: *mut LeanObject = core::ptr::null_mut();
    v_res_512_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0(v_x_511_);
    lean_dec_ref(v_x_511_);
    return v_res_512_;
}
pub unsafe fn l_Lake_instCoeOutKConfigDeclPartialBuildKey(
    mut v_k_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_515_: *mut LeanObject = core::ptr::null_mut();
    v___f_515_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0;
    return v___f_515_;
}
pub unsafe fn l_Lake_instCoeOutKConfigDeclPartialBuildKey___boxed(
    mut v_k_516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_517_: *mut LeanObject = core::ptr::null_mut();
    v_res_517_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey(v_k_516_);
    lean_dec(v_k_516_);
    return v_res_517_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x27___redArg(
    mut v_self_518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_519_: *mut LeanObject = core::ptr::null_mut();
    v_config_519_ = lean_ctor_get(v_self_518_, 3);
    lean_inc(v_config_519_);
    return v_config_519_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x27___redArg___boxed(
    mut v_self_520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_521_: *mut LeanObject = core::ptr::null_mut();
    v_res_521_ = l_Lake_PConfigDecl_config_x27___redArg(v_self_520_);
    lean_dec_ref(v_self_520_);
    return v_res_521_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x27(
    mut v_p_522_: *mut LeanObject,
    mut v_self_523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_524_: *mut LeanObject = core::ptr::null_mut();
    v_config_524_ = lean_ctor_get(v_self_523_, 3);
    lean_inc(v_config_524_);
    return v_config_524_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x27___boxed(
    mut v_p_525_: *mut LeanObject,
    mut v_self_526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_527_: *mut LeanObject = core::ptr::null_mut();
    v_res_527_ = l_Lake_PConfigDecl_config_x27(v_p_525_, v_self_526_);
    lean_dec_ref(v_self_526_);
    lean_dec(v_p_525_);
    return v_res_527_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x27___redArg(
    mut v_self_528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_529_: *mut LeanObject = core::ptr::null_mut();
    v_config_529_ = lean_ctor_get(v_self_528_, 3);
    lean_inc(v_config_529_);
    return v_config_529_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x27___redArg___boxed(
    mut v_self_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_531_: *mut LeanObject = core::ptr::null_mut();
    v_res_531_ = l_Lake_NConfigDecl_config_x27___redArg(v_self_530_);
    lean_dec_ref(v_self_530_);
    return v_res_531_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x27(
    mut v_p_532_: *mut LeanObject,
    mut v_n_533_: *mut LeanObject,
    mut v_self_534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_535_: *mut LeanObject = core::ptr::null_mut();
    v_config_535_ = lean_ctor_get(v_self_534_, 3);
    lean_inc(v_config_535_);
    return v_config_535_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x27___boxed(
    mut v_p_536_: *mut LeanObject,
    mut v_n_537_: *mut LeanObject,
    mut v_self_538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_539_: *mut LeanObject = core::ptr::null_mut();
    v_res_539_ = l_Lake_NConfigDecl_config_x27(v_p_536_, v_n_537_, v_self_538_);
    lean_dec_ref(v_self_538_);
    lean_dec(v_n_537_);
    lean_dec(v_p_536_);
    return v_res_539_;
}
pub unsafe fn l_Lake_ConfigDecl_config_x3f(
    mut v_kind_540_: *mut LeanObject,
    mut v_self_541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: u8 = 0;
    v_kind_542_ = lean_ctor_get(v_self_541_, 2);
    v_config_543_ = lean_ctor_get(v_self_541_, 3);
    v___x_544_ = lean_name_eq(v_kind_542_, v_kind_540_);
    if v___x_544_ == 0 {
        let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
        v___x_545_ = lean_box(0);
        return v___x_545_;
    } else {
        let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_543_);
        v___x_546_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_546_, 0, v_config_543_);
        return v___x_546_;
    }
}
pub unsafe fn l_Lake_ConfigDecl_config_x3f___boxed(
    mut v_kind_547_: *mut LeanObject,
    mut v_self_548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_549_: *mut LeanObject = core::ptr::null_mut();
    v_res_549_ = l_Lake_ConfigDecl_config_x3f(v_kind_547_, v_self_548_);
    lean_dec_ref(v_self_548_);
    lean_dec(v_kind_547_);
    return v_res_549_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x3f___redArg(
    mut v_kind_550_: *mut LeanObject,
    mut v_self_551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: u8 = 0;
    v_kind_552_ = lean_ctor_get(v_self_551_, 2);
    v_config_553_ = lean_ctor_get(v_self_551_, 3);
    v___x_554_ = lean_name_eq(v_kind_552_, v_kind_550_);
    if v___x_554_ == 0 {
        let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
        v___x_555_ = lean_box(0);
        return v___x_555_;
    } else {
        let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_553_);
        v___x_556_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_556_, 0, v_config_553_);
        return v___x_556_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_config_x3f___redArg___boxed(
    mut v_kind_557_: *mut LeanObject,
    mut v_self_558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_559_: *mut LeanObject = core::ptr::null_mut();
    v_res_559_ = l_Lake_PConfigDecl_config_x3f___redArg(v_kind_557_, v_self_558_);
    lean_dec_ref(v_self_558_);
    lean_dec(v_kind_557_);
    return v_res_559_;
}
pub unsafe fn l_Lake_PConfigDecl_config_x3f(
    mut v_p_560_: *mut LeanObject,
    mut v_kind_561_: *mut LeanObject,
    mut v_self_562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u8 = 0;
    v_kind_563_ = lean_ctor_get(v_self_562_, 2);
    v_config_564_ = lean_ctor_get(v_self_562_, 3);
    v___x_565_ = lean_name_eq(v_kind_563_, v_kind_561_);
    if v___x_565_ == 0 {
        let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
        v___x_566_ = lean_box(0);
        return v___x_566_;
    } else {
        let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_564_);
        v___x_567_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_567_, 0, v_config_564_);
        return v___x_567_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_config_x3f___boxed(
    mut v_p_568_: *mut LeanObject,
    mut v_kind_569_: *mut LeanObject,
    mut v_self_570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_571_: *mut LeanObject = core::ptr::null_mut();
    v_res_571_ = l_Lake_PConfigDecl_config_x3f(v_p_568_, v_kind_569_, v_self_570_);
    lean_dec_ref(v_self_570_);
    lean_dec(v_kind_569_);
    lean_dec(v_p_568_);
    return v_res_571_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x3f___redArg(
    mut v_kind_572_: *mut LeanObject,
    mut v_self_573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    v_kind_574_ = lean_ctor_get(v_self_573_, 2);
    v_config_575_ = lean_ctor_get(v_self_573_, 3);
    v___x_576_ = lean_name_eq(v_kind_574_, v_kind_572_);
    if v___x_576_ == 0 {
        let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
        v___x_577_ = lean_box(0);
        return v___x_577_;
    } else {
        let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_575_);
        v___x_578_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_578_, 0, v_config_575_);
        return v___x_578_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_config_x3f___redArg___boxed(
    mut v_kind_579_: *mut LeanObject,
    mut v_self_580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_581_: *mut LeanObject = core::ptr::null_mut();
    v_res_581_ = l_Lake_NConfigDecl_config_x3f___redArg(v_kind_579_, v_self_580_);
    lean_dec_ref(v_self_580_);
    lean_dec(v_kind_579_);
    return v_res_581_;
}
pub unsafe fn l_Lake_NConfigDecl_config_x3f(
    mut v_p_582_: *mut LeanObject,
    mut v_n_583_: *mut LeanObject,
    mut v_kind_584_: *mut LeanObject,
    mut v_self_585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    v_kind_586_ = lean_ctor_get(v_self_585_, 2);
    v_config_587_ = lean_ctor_get(v_self_585_, 3);
    v___x_588_ = lean_name_eq(v_kind_586_, v_kind_584_);
    if v___x_588_ == 0 {
        let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
        v___x_589_ = lean_box(0);
        return v___x_589_;
    } else {
        let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_587_);
        v___x_590_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_590_, 0, v_config_587_);
        return v___x_590_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_config_x3f___boxed(
    mut v_p_591_: *mut LeanObject,
    mut v_n_592_: *mut LeanObject,
    mut v_kind_593_: *mut LeanObject,
    mut v_self_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_595_: *mut LeanObject = core::ptr::null_mut();
    v_res_595_ = l_Lake_NConfigDecl_config_x3f(v_p_591_, v_n_592_, v_kind_593_, v_self_594_);
    lean_dec_ref(v_self_594_);
    lean_dec(v_kind_593_);
    lean_dec(v_n_592_);
    lean_dec(v_p_591_);
    return v_res_595_;
}
pub unsafe fn l_Lake_ConfigDecl_leanLibConfig_x3f(
    mut v_self_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: u8 = 0;
    v_kind_600_ = lean_ctor_get(v_self_599_, 2);
    v_config_601_ = lean_ctor_get(v_self_599_, 3);
    v___x_602_ = l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1;
    v___x_603_ = lean_name_eq(v_kind_600_, v___x_602_);
    if v___x_603_ == 0 {
        let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
        v___x_604_ = lean_box(0);
        return v___x_604_;
    } else {
        let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_601_);
        v___x_605_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_605_, 0, v_config_601_);
        return v___x_605_;
    }
}
pub unsafe fn l_Lake_ConfigDecl_leanLibConfig_x3f___boxed(
    mut v_self_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_607_: *mut LeanObject = core::ptr::null_mut();
    v_res_607_ = l_Lake_ConfigDecl_leanLibConfig_x3f(v_self_606_);
    lean_dec_ref(v_self_606_);
    return v_res_607_;
}
pub unsafe fn l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(
    mut v_self_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: u8 = 0;
    v_kind_609_ = lean_ctor_get(v_self_608_, 2);
    v_config_610_ = lean_ctor_get(v_self_608_, 3);
    v___x_611_ = l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1;
    v___x_612_ = lean_name_eq(v_kind_609_, v___x_611_);
    if v___x_612_ == 0 {
        let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
        v___x_613_ = lean_box(0);
        return v___x_613_;
    } else {
        let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_610_);
        v___x_614_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_614_, 0, v_config_610_);
        return v___x_614_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_leanLibConfig_x3f___redArg___boxed(
    mut v_self_615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_616_: *mut LeanObject = core::ptr::null_mut();
    v_res_616_ = l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(v_self_615_);
    lean_dec_ref(v_self_615_);
    return v_res_616_;
}
pub unsafe fn l_Lake_NConfigDecl_leanLibConfig_x3f(
    mut v_p_617_: *mut LeanObject,
    mut v_n_618_: *mut LeanObject,
    mut v_self_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: u8 = 0;
    v_kind_620_ = lean_ctor_get(v_self_619_, 2);
    v_config_621_ = lean_ctor_get(v_self_619_, 3);
    v___x_622_ = l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1;
    v___x_623_ = lean_name_eq(v_kind_620_, v___x_622_);
    if v___x_623_ == 0 {
        let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
        v___x_624_ = lean_box(0);
        return v___x_624_;
    } else {
        let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_621_);
        v___x_625_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_625_, 0, v_config_621_);
        return v___x_625_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_leanLibConfig_x3f___boxed(
    mut v_p_626_: *mut LeanObject,
    mut v_n_627_: *mut LeanObject,
    mut v_self_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_629_: *mut LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Lake_NConfigDecl_leanLibConfig_x3f(v_p_626_, v_n_627_, v_self_628_);
    lean_dec_ref(v_self_628_);
    lean_dec(v_n_627_);
    lean_dec(v_p_626_);
    return v_res_629_;
}
pub unsafe fn l_Lake_ConfigDecl_leanExeConfig_x3f(
    mut v_self_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    v_kind_631_ = lean_ctor_get(v_self_630_, 2);
    v_config_632_ = lean_ctor_get(v_self_630_, 3);
    v___x_633_ = l_Lake_LeanExe_keyword;
    v___x_634_ = lean_name_eq(v_kind_631_, v___x_633_);
    if v___x_634_ == 0 {
        let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
        v___x_635_ = lean_box(0);
        return v___x_635_;
    } else {
        let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_632_);
        v___x_636_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_636_, 0, v_config_632_);
        return v___x_636_;
    }
}
pub unsafe fn l_Lake_ConfigDecl_leanExeConfig_x3f___boxed(
    mut v_self_637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_638_: *mut LeanObject = core::ptr::null_mut();
    v_res_638_ = l_Lake_ConfigDecl_leanExeConfig_x3f(v_self_637_);
    lean_dec_ref(v_self_637_);
    return v_res_638_;
}
pub unsafe fn l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(
    mut v_self_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    v_kind_640_ = lean_ctor_get(v_self_639_, 2);
    v_config_641_ = lean_ctor_get(v_self_639_, 3);
    v___x_642_ = l_Lake_LeanExe_keyword;
    v___x_643_ = lean_name_eq(v_kind_640_, v___x_642_);
    if v___x_643_ == 0 {
        let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
        v___x_644_ = lean_box(0);
        return v___x_644_;
    } else {
        let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_641_);
        v___x_645_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_645_, 0, v_config_641_);
        return v___x_645_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_leanExeConfig_x3f___redArg___boxed(
    mut v_self_646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_647_: *mut LeanObject = core::ptr::null_mut();
    v_res_647_ = l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(v_self_646_);
    lean_dec_ref(v_self_646_);
    return v_res_647_;
}
pub unsafe fn l_Lake_NConfigDecl_leanExeConfig_x3f(
    mut v_p_648_: *mut LeanObject,
    mut v_n_649_: *mut LeanObject,
    mut v_self_650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: u8 = 0;
    v_kind_651_ = lean_ctor_get(v_self_650_, 2);
    v_config_652_ = lean_ctor_get(v_self_650_, 3);
    v___x_653_ = l_Lake_LeanExe_keyword;
    v___x_654_ = lean_name_eq(v_kind_651_, v___x_653_);
    if v___x_654_ == 0 {
        let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
        v___x_655_ = lean_box(0);
        return v___x_655_;
    } else {
        let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_652_);
        v___x_656_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_656_, 0, v_config_652_);
        return v___x_656_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_leanExeConfig_x3f___boxed(
    mut v_p_657_: *mut LeanObject,
    mut v_n_658_: *mut LeanObject,
    mut v_self_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_660_: *mut LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Lake_NConfigDecl_leanExeConfig_x3f(v_p_657_, v_n_658_, v_self_659_);
    lean_dec_ref(v_self_659_);
    lean_dec(v_n_658_);
    lean_dec(v_p_657_);
    return v_res_660_;
}
pub unsafe fn l_Lake_PConfigDecl_externLibConfig_x3f___redArg(
    mut v_self_661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: u8 = 0;
    v_kind_662_ = lean_ctor_get(v_self_661_, 2);
    v_config_663_ = lean_ctor_get(v_self_661_, 3);
    v___x_664_ = l_Lake_ExternLib_keyword;
    v___x_665_ = lean_name_eq(v_kind_662_, v___x_664_);
    if v___x_665_ == 0 {
        let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
        v___x_666_ = lean_box(0);
        return v___x_666_;
    } else {
        let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_663_);
        v___x_667_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_667_, 0, v_config_663_);
        return v___x_667_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_externLibConfig_x3f___redArg___boxed(
    mut v_self_668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_669_: *mut LeanObject = core::ptr::null_mut();
    v_res_669_ = l_Lake_PConfigDecl_externLibConfig_x3f___redArg(v_self_668_);
    lean_dec_ref(v_self_668_);
    return v_res_669_;
}
pub unsafe fn l_Lake_PConfigDecl_externLibConfig_x3f(
    mut v_p_670_: *mut LeanObject,
    mut v_self_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: u8 = 0;
    v_kind_672_ = lean_ctor_get(v_self_671_, 2);
    v_config_673_ = lean_ctor_get(v_self_671_, 3);
    v___x_674_ = l_Lake_ExternLib_keyword;
    v___x_675_ = lean_name_eq(v_kind_672_, v___x_674_);
    if v___x_675_ == 0 {
        let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
        v___x_676_ = lean_box(0);
        return v___x_676_;
    } else {
        let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_673_);
        v___x_677_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_677_, 0, v_config_673_);
        return v___x_677_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_externLibConfig_x3f___boxed(
    mut v_p_678_: *mut LeanObject,
    mut v_self_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_680_: *mut LeanObject = core::ptr::null_mut();
    v_res_680_ = l_Lake_PConfigDecl_externLibConfig_x3f(v_p_678_, v_self_679_);
    lean_dec_ref(v_self_679_);
    lean_dec(v_p_678_);
    return v_res_680_;
}
pub unsafe fn l_Lake_NConfigDecl_externLibConfig_x3f___redArg(
    mut v_self_681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    v_kind_682_ = lean_ctor_get(v_self_681_, 2);
    v_config_683_ = lean_ctor_get(v_self_681_, 3);
    v___x_684_ = l_Lake_ExternLib_keyword;
    v___x_685_ = lean_name_eq(v_kind_682_, v___x_684_);
    if v___x_685_ == 0 {
        let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
        v___x_686_ = lean_box(0);
        return v___x_686_;
    } else {
        let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_683_);
        v___x_687_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_687_, 0, v_config_683_);
        return v___x_687_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_externLibConfig_x3f___redArg___boxed(
    mut v_self_688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_689_: *mut LeanObject = core::ptr::null_mut();
    v_res_689_ = l_Lake_NConfigDecl_externLibConfig_x3f___redArg(v_self_688_);
    lean_dec_ref(v_self_688_);
    return v_res_689_;
}
pub unsafe fn l_Lake_NConfigDecl_externLibConfig_x3f(
    mut v_p_690_: *mut LeanObject,
    mut v_n_691_: *mut LeanObject,
    mut v_self_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: u8 = 0;
    v_kind_693_ = lean_ctor_get(v_self_692_, 2);
    v_config_694_ = lean_ctor_get(v_self_692_, 3);
    v___x_695_ = l_Lake_ExternLib_keyword;
    v___x_696_ = lean_name_eq(v_kind_693_, v___x_695_);
    if v___x_696_ == 0 {
        let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
        v___x_697_ = lean_box(0);
        return v___x_697_;
    } else {
        let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_694_);
        v___x_698_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_698_, 0, v_config_694_);
        return v___x_698_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_externLibConfig_x3f___boxed(
    mut v_p_699_: *mut LeanObject,
    mut v_n_700_: *mut LeanObject,
    mut v_self_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_702_: *mut LeanObject = core::ptr::null_mut();
    v_res_702_ = l_Lake_NConfigDecl_externLibConfig_x3f(v_p_699_, v_n_700_, v_self_701_);
    lean_dec_ref(v_self_701_);
    lean_dec(v_n_700_);
    lean_dec(v_p_699_);
    return v_res_702_;
}
pub unsafe fn l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg(
    mut v_kind_708_: *mut LeanObject,
    mut v_h__1_709_: *mut LeanObject,
    mut v_h__2_710_: *mut LeanObject,
    mut v_h__3_711_: *mut LeanObject,
    mut v_h__4_712_: *mut LeanObject,
    mut v_h__5_713_: *mut LeanObject,
    mut v_h__6_714_: *mut LeanObject,
    mut v_h__7_715_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_kind_708_) {
        1 => {
            let mut v_pre_716_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_712_);
            v_pre_716_ = lean_ctor_get(v_kind_708_, 0);
            if lean_obj_tag(v_pre_716_) == 0 {
                let mut v_str_717_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_719_: u8 = 0;
                v_str_717_ = lean_ctor_get(v_kind_708_, 1);
                v___x_718_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0;
                v___x_719_ = lean_string_dec_eq(v_str_717_, v___x_718_);
                if v___x_719_ == 0 {
                    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_721_: u8 = 0;
                    lean_dec(v_h__1_709_);
                    v___x_720_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1;
                    v___x_721_ = lean_string_dec_eq(v_str_717_, v___x_720_);
                    if v___x_721_ == 0 {
                        let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_723_: u8 = 0;
                        lean_dec(v_h__2_710_);
                        v___x_722_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2;
                        v___x_723_ = lean_string_dec_eq(v_str_717_, v___x_722_);
                        if v___x_723_ == 0 {
                            let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_725_: u8 = 0;
                            lean_dec(v_h__3_711_);
                            v___x_724_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3;
                            v___x_725_ = lean_string_dec_eq(v_str_717_, v___x_724_);
                            if v___x_725_ == 0 {
                                let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_727_: u8 = 0;
                                lean_dec(v_h__5_713_);
                                v___x_726_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4;
                                v___x_727_ = lean_string_dec_eq(v_str_717_, v___x_726_);
                                if v___x_727_ == 0 {
                                    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
                                    lean_dec(v_h__6_714_);
                                    v___x_728_ = lean_apply_7(
                                        v_h__7_715_,
                                        v_kind_708_,
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                    );
                                    return v___x_728_;
                                } else {
                                    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
                                    lean_dec_ref_known(v_kind_708_, 2);
                                    lean_dec(v_h__7_715_);
                                    v___x_729_ = lean_box(0);
                                    v___x_730_ = lean_apply_1(v_h__6_714_, v___x_729_);
                                    return v___x_730_;
                                }
                            } else {
                                let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
                                lean_dec_ref_known(v_kind_708_, 2);
                                lean_dec(v_h__7_715_);
                                lean_dec(v_h__6_714_);
                                v___x_731_ = lean_box(0);
                                v___x_732_ = lean_apply_1(v_h__5_713_, v___x_731_);
                                return v___x_732_;
                            }
                        } else {
                            let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref_known(v_kind_708_, 2);
                            lean_dec(v_h__7_715_);
                            lean_dec(v_h__6_714_);
                            lean_dec(v_h__5_713_);
                            v___x_733_ = lean_box(0);
                            v___x_734_ = lean_apply_1(v_h__3_711_, v___x_733_);
                            return v___x_734_;
                        }
                    } else {
                        let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v_kind_708_, 2);
                        lean_dec(v_h__7_715_);
                        lean_dec(v_h__6_714_);
                        lean_dec(v_h__5_713_);
                        lean_dec(v_h__3_711_);
                        v___x_735_ = lean_box(0);
                        v___x_736_ = lean_apply_1(v_h__2_710_, v___x_735_);
                        return v___x_736_;
                    }
                } else {
                    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v_kind_708_, 2);
                    lean_dec(v_h__7_715_);
                    lean_dec(v_h__6_714_);
                    lean_dec(v_h__5_713_);
                    lean_dec(v_h__3_711_);
                    lean_dec(v_h__2_710_);
                    v___x_737_ = lean_box(0);
                    v___x_738_ = lean_apply_1(v_h__1_709_, v___x_737_);
                    return v___x_738_;
                }
            } else {
                let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__6_714_);
                lean_dec(v_h__5_713_);
                lean_dec(v_h__3_711_);
                lean_dec(v_h__2_710_);
                lean_dec(v_h__1_709_);
                v___x_739_ = lean_apply_7(
                    v_h__7_715_,
                    v_kind_708_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_739_;
            }
        }
        0 => {
            let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_715_);
            lean_dec(v_h__6_714_);
            lean_dec(v_h__5_713_);
            lean_dec(v_h__3_711_);
            lean_dec(v_h__2_710_);
            lean_dec(v_h__1_709_);
            v___x_740_ = lean_box(0);
            v___x_741_ = lean_apply_1(v_h__4_712_, v___x_740_);
            return v___x_741_;
        }
        _ => {
            let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_714_);
            lean_dec(v_h__5_713_);
            lean_dec(v_h__4_712_);
            lean_dec(v_h__3_711_);
            lean_dec(v_h__2_710_);
            lean_dec(v_h__1_709_);
            v___x_742_ = lean_apply_7(
                v_h__7_715_,
                v_kind_708_,
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
            );
            return v___x_742_;
        }
    }
}
pub unsafe fn l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter(
    mut v_motive_743_: *mut LeanObject,
    mut v_kind_744_: *mut LeanObject,
    mut v_h__1_745_: *mut LeanObject,
    mut v_h__2_746_: *mut LeanObject,
    mut v_h__3_747_: *mut LeanObject,
    mut v_h__4_748_: *mut LeanObject,
    mut v_h__5_749_: *mut LeanObject,
    mut v_h__6_750_: *mut LeanObject,
    mut v_h__7_751_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_kind_744_) {
        1 => {
            let mut v_pre_752_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_748_);
            v_pre_752_ = lean_ctor_get(v_kind_744_, 0);
            if lean_obj_tag(v_pre_752_) == 0 {
                let mut v_str_753_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_755_: u8 = 0;
                v_str_753_ = lean_ctor_get(v_kind_744_, 1);
                v___x_754_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0;
                v___x_755_ = lean_string_dec_eq(v_str_753_, v___x_754_);
                if v___x_755_ == 0 {
                    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_757_: u8 = 0;
                    lean_dec(v_h__1_745_);
                    v___x_756_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1;
                    v___x_757_ = lean_string_dec_eq(v_str_753_, v___x_756_);
                    if v___x_757_ == 0 {
                        let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_759_: u8 = 0;
                        lean_dec(v_h__2_746_);
                        v___x_758_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2;
                        v___x_759_ = lean_string_dec_eq(v_str_753_, v___x_758_);
                        if v___x_759_ == 0 {
                            let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_761_: u8 = 0;
                            lean_dec(v_h__3_747_);
                            v___x_760_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3;
                            v___x_761_ = lean_string_dec_eq(v_str_753_, v___x_760_);
                            if v___x_761_ == 0 {
                                let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_763_: u8 = 0;
                                lean_dec(v_h__5_749_);
                                v___x_762_ = l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4;
                                v___x_763_ = lean_string_dec_eq(v_str_753_, v___x_762_);
                                if v___x_763_ == 0 {
                                    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
                                    lean_dec(v_h__6_750_);
                                    v___x_764_ = lean_apply_7(
                                        v_h__7_751_,
                                        v_kind_744_,
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                    );
                                    return v___x_764_;
                                } else {
                                    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
                                    lean_dec_ref_known(v_kind_744_, 2);
                                    lean_dec(v_h__7_751_);
                                    v___x_765_ = lean_box(0);
                                    v___x_766_ = lean_apply_1(v_h__6_750_, v___x_765_);
                                    return v___x_766_;
                                }
                            } else {
                                let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
                                lean_dec_ref_known(v_kind_744_, 2);
                                lean_dec(v_h__7_751_);
                                lean_dec(v_h__6_750_);
                                v___x_767_ = lean_box(0);
                                v___x_768_ = lean_apply_1(v_h__5_749_, v___x_767_);
                                return v___x_768_;
                            }
                        } else {
                            let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref_known(v_kind_744_, 2);
                            lean_dec(v_h__7_751_);
                            lean_dec(v_h__6_750_);
                            lean_dec(v_h__5_749_);
                            v___x_769_ = lean_box(0);
                            v___x_770_ = lean_apply_1(v_h__3_747_, v___x_769_);
                            return v___x_770_;
                        }
                    } else {
                        let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v_kind_744_, 2);
                        lean_dec(v_h__7_751_);
                        lean_dec(v_h__6_750_);
                        lean_dec(v_h__5_749_);
                        lean_dec(v_h__3_747_);
                        v___x_771_ = lean_box(0);
                        v___x_772_ = lean_apply_1(v_h__2_746_, v___x_771_);
                        return v___x_772_;
                    }
                } else {
                    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v_kind_744_, 2);
                    lean_dec(v_h__7_751_);
                    lean_dec(v_h__6_750_);
                    lean_dec(v_h__5_749_);
                    lean_dec(v_h__3_747_);
                    lean_dec(v_h__2_746_);
                    v___x_773_ = lean_box(0);
                    v___x_774_ = lean_apply_1(v_h__1_745_, v___x_773_);
                    return v___x_774_;
                }
            } else {
                let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__6_750_);
                lean_dec(v_h__5_749_);
                lean_dec(v_h__3_747_);
                lean_dec(v_h__2_746_);
                lean_dec(v_h__1_745_);
                v___x_775_ = lean_apply_7(
                    v_h__7_751_,
                    v_kind_744_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_775_;
            }
        }
        0 => {
            let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_751_);
            lean_dec(v_h__6_750_);
            lean_dec(v_h__5_749_);
            lean_dec(v_h__3_747_);
            lean_dec(v_h__2_746_);
            lean_dec(v_h__1_745_);
            v___x_776_ = lean_box(0);
            v___x_777_ = lean_apply_1(v_h__4_748_, v___x_776_);
            return v___x_777_;
        }
        _ => {
            let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_750_);
            lean_dec(v_h__5_749_);
            lean_dec(v_h__4_748_);
            lean_dec(v_h__3_747_);
            lean_dec(v_h__2_746_);
            lean_dec(v_h__1_745_);
            v___x_778_ = lean_apply_7(
                v_h__7_751_,
                v_kind_744_,
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
            );
            return v___x_778_;
        }
    }
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig___redArg(
    mut v_self_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_780_: *mut LeanObject = core::ptr::null_mut();
    v_config_780_ = lean_ctor_get(v_self_779_, 3);
    lean_inc(v_config_780_);
    return v_config_780_;
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig___redArg___boxed(
    mut v_self_781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_782_: *mut LeanObject = core::ptr::null_mut();
    v_res_782_ = l_Lake_PConfigDecl_opaqueTargetConfig___redArg(v_self_781_);
    lean_dec_ref(v_self_781_);
    return v_res_782_;
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig(
    mut v_p_783_: *mut LeanObject,
    mut v_self_784_: *mut LeanObject,
    mut v_h_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_786_: *mut LeanObject = core::ptr::null_mut();
    v_config_786_ = lean_ctor_get(v_self_784_, 3);
    lean_inc(v_config_786_);
    return v_config_786_;
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig___boxed(
    mut v_p_787_: *mut LeanObject,
    mut v_self_788_: *mut LeanObject,
    mut v_h_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_790_: *mut LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Lake_PConfigDecl_opaqueTargetConfig(v_p_787_, v_self_788_, v_h_789_);
    lean_dec_ref(v_self_788_);
    lean_dec(v_p_787_);
    return v_res_790_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig___redArg(
    mut v_self_791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_792_: *mut LeanObject = core::ptr::null_mut();
    v_config_792_ = lean_ctor_get(v_self_791_, 3);
    lean_inc(v_config_792_);
    return v_config_792_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig___redArg___boxed(
    mut v_self_793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_794_: *mut LeanObject = core::ptr::null_mut();
    v_res_794_ = l_Lake_NConfigDecl_opaqueTargetConfig___redArg(v_self_793_);
    lean_dec_ref(v_self_793_);
    return v_res_794_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig(
    mut v_p_795_: *mut LeanObject,
    mut v_n_796_: *mut LeanObject,
    mut v_self_797_: *mut LeanObject,
    mut v_h_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_799_: *mut LeanObject = core::ptr::null_mut();
    v_config_799_ = lean_ctor_get(v_self_797_, 3);
    lean_inc(v_config_799_);
    return v_config_799_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig___boxed(
    mut v_p_800_: *mut LeanObject,
    mut v_n_801_: *mut LeanObject,
    mut v_self_802_: *mut LeanObject,
    mut v_h_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_804_: *mut LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Lake_NConfigDecl_opaqueTargetConfig(v_p_800_, v_n_801_, v_self_802_, v_h_803_);
    lean_dec_ref(v_self_802_);
    lean_dec(v_n_801_);
    lean_dec(v_p_800_);
    return v_res_804_;
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(
    mut v_self_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: u8 = 0;
    v_kind_806_ = lean_ctor_get(v_self_805_, 2);
    v_config_807_ = lean_ctor_get(v_self_805_, 3);
    v___x_808_ = l_Lean_Name_isAnonymous(v_kind_806_);
    if v___x_808_ == 0 {
        let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
        v___x_809_ = lean_box(0);
        return v___x_809_;
    } else {
        let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_807_);
        v___x_810_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_810_, 0, v_config_807_);
        return v___x_810_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(
    mut v_self_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_812_: *mut LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(v_self_811_);
    lean_dec_ref(v_self_811_);
    return v_res_812_;
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig_x3f(
    mut v_p_813_: *mut LeanObject,
    mut v_self_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: u8 = 0;
    v_kind_815_ = lean_ctor_get(v_self_814_, 2);
    v_config_816_ = lean_ctor_get(v_self_814_, 3);
    v___x_817_ = l_Lean_Name_isAnonymous(v_kind_815_);
    if v___x_817_ == 0 {
        let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
        v___x_818_ = lean_box(0);
        return v___x_818_;
    } else {
        let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_816_);
        v___x_819_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_819_, 0, v_config_816_);
        return v___x_819_;
    }
}
pub unsafe fn l_Lake_PConfigDecl_opaqueTargetConfig_x3f___boxed(
    mut v_p_820_: *mut LeanObject,
    mut v_self_821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_822_: *mut LeanObject = core::ptr::null_mut();
    v_res_822_ = l_Lake_PConfigDecl_opaqueTargetConfig_x3f(v_p_820_, v_self_821_);
    lean_dec_ref(v_self_821_);
    lean_dec(v_p_820_);
    return v_res_822_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(
    mut v_self_823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: u8 = 0;
    v_kind_824_ = lean_ctor_get(v_self_823_, 2);
    v_config_825_ = lean_ctor_get(v_self_823_, 3);
    v___x_826_ = l_Lean_Name_isAnonymous(v_kind_824_);
    if v___x_826_ == 0 {
        let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
        v___x_827_ = lean_box(0);
        return v___x_827_;
    } else {
        let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_825_);
        v___x_828_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_828_, 0, v_config_825_);
        return v___x_828_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(
    mut v_self_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_830_: *mut LeanObject = core::ptr::null_mut();
    v_res_830_ = l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(v_self_829_);
    lean_dec_ref(v_self_829_);
    return v_res_830_;
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig_x3f(
    mut v_p_831_: *mut LeanObject,
    mut v_n_832_: *mut LeanObject,
    mut v_self_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: u8 = 0;
    v_kind_834_ = lean_ctor_get(v_self_833_, 2);
    v_config_835_ = lean_ctor_get(v_self_833_, 3);
    v___x_836_ = l_Lean_Name_isAnonymous(v_kind_834_);
    if v___x_836_ == 0 {
        let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
        v___x_837_ = lean_box(0);
        return v___x_837_;
    } else {
        let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_835_);
        v___x_838_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_838_, 0, v_config_835_);
        return v___x_838_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_opaqueTargetConfig_x3f___boxed(
    mut v_p_839_: *mut LeanObject,
    mut v_n_840_: *mut LeanObject,
    mut v_self_841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_842_: *mut LeanObject = core::ptr::null_mut();
    v_res_842_ = l_Lake_NConfigDecl_opaqueTargetConfig_x3f(v_p_839_, v_n_840_, v_self_841_);
    lean_dec_ref(v_self_841_);
    lean_dec(v_n_840_);
    lean_dec(v_p_839_);
    return v_res_842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_ConfigDecl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanLibConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLibConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFileConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_ConfigDecl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lake_PConfigDecl_pkg__eq___autoParam = _init_l_Lake_PConfigDecl_pkg__eq___autoParam();
    lean_mark_persistent(l_Lake_PConfigDecl_pkg__eq___autoParam);
    l_Lake_NConfigDecl_name__eq___autoParam = _init_l_Lake_NConfigDecl_name__eq___autoParam();
    lean_mark_persistent(l_Lake_NConfigDecl_name__eq___autoParam);
    l_Lake_KConfigDecl_kind__eq___autoParam = _init_l_Lake_KConfigDecl_kind__eq___autoParam();
    lean_mark_persistent(l_Lake_KConfigDecl_kind__eq___autoParam);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_ConfigDecl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LeanLibConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LeanExeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_ExternLibConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_InputFileConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ConfigDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_ConfigDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_ConfigDecl(builtin);
}

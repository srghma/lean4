// Lean compiler output
// Module: Init.Grind.Tactics
// Imports: Init.Core Init.Grind.Interactive
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Grind::Interactive::{
    initialize_Init_Grind_Interactive, l_Lean_Parser_Tactic_Grind_grindSeq,
    l_Lean_Parser_Tactic_grindParam, runtime_initialize_Init_Grind_Interactive,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4};
use crate::r#gen::Init::Tactics::l_Lean_Parser_Tactic_optConfig;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_unsigned_to_nat,
};
pub static l_Lean_Parser_Tactic_grind___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Parser_Tactic_grind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Parser_Tactic_grind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Parser_Tactic_grind___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__3_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [103, 114, 105, 110, 100, 0],
};
static mut l_Lean_Parser_Tactic_grind___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__3_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_grind___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_grind___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_grind___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_grind___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__3_value) as *mut LeanObject,
        7213727686127018646 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grind___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__5_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_Lean_Parser_Tactic_grind___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__5_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grind___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__3_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grind___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__7_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__9_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
};
static mut l_Lean_Parser_Tactic_grind___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__9_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grind___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__11_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 111, 110, 108, 121, 0],
};
static mut l_Lean_Parser_Tactic_grind___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__12_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__11_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grind___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__13_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grind___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__13_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__15_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 91, 0],
};
static mut l_Lean_Parser_Tactic_grind___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__16_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__15_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_grind___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__17_value: LeanStringObject<16> = LeanStringObject {
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
        119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Parser_Tactic_grind___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__18_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__17_value) as *mut LeanObject,
        1164644006045091397 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grind___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__18_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__19_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Lean_Parser_Tactic_grind___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__19_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__20_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_Lean_Parser_Tactic_grind___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__21_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__20_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_grind___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__21_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__25_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l_Lean_Parser_Tactic_grind___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__25_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__26_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__25_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_grind___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__26_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__27: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__28: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__29: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind___closed__30_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 61, 62, 32, 0],
};
static mut l_Lean_Parser_Tactic_grind___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__30_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind___closed__31_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__30_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_grind___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__31_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grind___closed__32_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__32: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__33_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__33: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__34_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__34: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind___closed__35_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind___closed__35: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grind: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grindTrace___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [103, 114, 105, 110, 100, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grindTrace___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__0_value) as *mut LeanObject,
        8341917469546378704 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindTrace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindTrace___closed__2_value: LeanStringObject<7> =
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
        m_data: [103, 114, 105, 110, 100, 63, 0],
    };
static mut l_Lean_Parser_Tactic_grindTrace___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grindTrace___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grindTrace___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grindTrace___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grindTrace___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindTrace___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindTrace___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindTrace___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindTrace___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindTrace___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grindTrace___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grindTrace___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grindTrace: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_sym___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [115, 121, 109, 0],
};
static mut l_Lean_Parser_Tactic_sym___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_sym___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_sym___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_sym___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_sym___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__0_value) as *mut LeanObject,
        2698983533533738959 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_sym___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_sym___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_sym___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_sym___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_sym___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_sym___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_sym___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_sym___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_sym___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_sym___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_sym___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_sym___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_sym: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_cutsat___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 117, 116, 115, 97, 116, 0],
};
static mut l_Lean_Parser_Tactic_cutsat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_cutsat___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__0_value) as *mut LeanObject,
        2518545331120607024 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_cutsat___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_cutsat___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_cutsat___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_cutsat___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_cutsat___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_cutsat___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_cutsat___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_cutsat___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_cutsat: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_lia___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [108, 105, 97, 0],
};
static mut l_Lean_Parser_Tactic_lia___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_lia___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_lia___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_lia___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_lia___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__0_value) as *mut LeanObject,
        628853965465602645 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_lia___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_lia___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_lia___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_lia___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_lia___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_lia___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_lia___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_lia___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_lia: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind__order___closed__0_value: LeanStringObject<12> =
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
        m_data: [103, 114, 105, 110, 100, 95, 111, 114, 100, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grind__order___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__0_value)
                as *mut LeanObject,
            6376312911296474159 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind__order___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__order___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__order___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grind__order___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind__order___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind__order___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind__order___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grind__order: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grind__linarith___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            103, 114, 105, 110, 100, 95, 108, 105, 110, 97, 114, 105, 116, 104, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value) as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_grind__linarith___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__0_value)
                as *mut LeanObject,
            6166429773221086783 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grind__linarith___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_grind__linarith___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grind__linarith___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grind__linarith___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind__linarith___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grind__linarith___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grind__linarith___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grind__linarith: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_grobner___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [103, 114, 111, 98, 110, 101, 114, 0],
};
static mut l_Lean_Parser_Tactic_grobner___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_grobner___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_grobner___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_grobner___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grind___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_grobner___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__0_value) as *mut LeanObject,
        12002129749639216369 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grobner___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_grobner___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_grobner___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_grobner___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_grobner___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grobner___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_grobner___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_grobner___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_grobner: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__8() -> *mut LeanObject {
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    v___x_255_ = l_Lean_Parser_Tactic_optConfig;
    v___x_256_ = l_Lean_Parser_Tactic_grind___closed__7;
    v___x_257_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_258_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_258_, 0, v___x_257_);
    lean_ctor_set(v___x_258_, 1, v___x_256_);
    lean_ctor_set(v___x_258_, 2, v___x_255_);
    return v___x_258_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__14() -> *mut LeanObject {
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v___x_269_ = l_Lean_Parser_Tactic_grind___closed__13;
    v___x_270_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__8_once),
        _init_l_Lean_Parser_Tactic_grind___closed__8,
    );
    v___x_271_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_272_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_272_, 0, v___x_271_);
    lean_ctor_set(v___x_272_, 1, v___x_270_);
    lean_ctor_set(v___x_272_, 2, v___x_269_);
    return v___x_272_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__22() -> *mut LeanObject {
    let mut v___x_283_: u8 = 0;
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    v___x_283_ = 0;
    v___x_284_ = l_Lean_Parser_Tactic_grind___closed__21;
    v___x_285_ = l_Lean_Parser_Tactic_grind___closed__19;
    v___x_286_ = l_Lean_Parser_Tactic_grindParam;
    v___x_287_ = lean_alloc_ctor(10, 3, (1) as u32);
    lean_ctor_set(v___x_287_, 0, v___x_286_);
    lean_ctor_set(v___x_287_, 1, v___x_285_);
    lean_ctor_set(v___x_287_, 2, v___x_284_);
    lean_ctor_set_uint8(
        v___x_287_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_283_,
    );
    return v___x_287_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__23() -> *mut LeanObject {
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    v___x_288_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__22_once),
        _init_l_Lean_Parser_Tactic_grind___closed__22,
    );
    v___x_289_ = l_Lean_Parser_Tactic_grind___closed__18;
    v___x_290_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_290_, 0, v___x_289_);
    lean_ctor_set(v___x_290_, 1, v___x_288_);
    return v___x_290_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__24() -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    v___x_291_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__23_once),
        _init_l_Lean_Parser_Tactic_grind___closed__23,
    );
    v___x_292_ = l_Lean_Parser_Tactic_grind___closed__16;
    v___x_293_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_294_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_294_, 0, v___x_293_);
    lean_ctor_set(v___x_294_, 1, v___x_292_);
    lean_ctor_set(v___x_294_, 2, v___x_291_);
    return v___x_294_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__27() -> *mut LeanObject {
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    v___x_298_ = l_Lean_Parser_Tactic_grind___closed__26;
    v___x_299_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__24_once),
        _init_l_Lean_Parser_Tactic_grind___closed__24,
    );
    v___x_300_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_301_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_301_, 0, v___x_300_);
    lean_ctor_set(v___x_301_, 1, v___x_299_);
    lean_ctor_set(v___x_301_, 2, v___x_298_);
    return v___x_301_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__28() -> *mut LeanObject {
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    v___x_302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__27_once),
        _init_l_Lean_Parser_Tactic_grind___closed__27,
    );
    v___x_303_ = l_Lean_Parser_Tactic_grind___closed__10;
    v___x_304_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_304_, 0, v___x_303_);
    lean_ctor_set(v___x_304_, 1, v___x_302_);
    return v___x_304_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__29() -> *mut LeanObject {
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    v___x_305_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28_once),
        _init_l_Lean_Parser_Tactic_grind___closed__28,
    );
    v___x_306_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__14_once),
        _init_l_Lean_Parser_Tactic_grind___closed__14,
    );
    v___x_307_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_308_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_308_, 0, v___x_307_);
    lean_ctor_set(v___x_308_, 1, v___x_306_);
    lean_ctor_set(v___x_308_, 2, v___x_305_);
    return v___x_308_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__32() -> *mut LeanObject {
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    v___x_312_ = l_Lean_Parser_Tactic_Grind_grindSeq;
    v___x_313_ = l_Lean_Parser_Tactic_grind___closed__31;
    v___x_314_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_315_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_315_, 0, v___x_314_);
    lean_ctor_set(v___x_315_, 1, v___x_313_);
    lean_ctor_set(v___x_315_, 2, v___x_312_);
    return v___x_315_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__33() -> *mut LeanObject {
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    v___x_316_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__32_once),
        _init_l_Lean_Parser_Tactic_grind___closed__32,
    );
    v___x_317_ = l_Lean_Parser_Tactic_grind___closed__10;
    v___x_318_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_318_, 0, v___x_317_);
    lean_ctor_set(v___x_318_, 1, v___x_316_);
    return v___x_318_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__34() -> *mut LeanObject {
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    v___x_319_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__33),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__33_once),
        _init_l_Lean_Parser_Tactic_grind___closed__33,
    );
    v___x_320_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__29_once),
        _init_l_Lean_Parser_Tactic_grind___closed__29,
    );
    v___x_321_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_322_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_322_, 0, v___x_321_);
    lean_ctor_set(v___x_322_, 1, v___x_320_);
    lean_ctor_set(v___x_322_, 2, v___x_319_);
    return v___x_322_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind___closed__35() -> *mut LeanObject {
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    v___x_323_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__34_once),
        _init_l_Lean_Parser_Tactic_grind___closed__34,
    );
    v___x_324_ = lean_unsigned_to_nat(1022);
    v___x_325_ = l_Lean_Parser_Tactic_grind___closed__4;
    v___x_326_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_326_, 0, v___x_325_);
    lean_ctor_set(v___x_326_, 1, v___x_324_);
    lean_ctor_set(v___x_326_, 2, v___x_323_);
    return v___x_326_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind() -> *mut LeanObject {
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    v___x_327_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__35_once),
        _init_l_Lean_Parser_Tactic_grind___closed__35,
    );
    return v___x_327_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__4() -> *mut LeanObject {
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    v___x_338_ = l_Lean_Parser_Tactic_optConfig;
    v___x_339_ = l_Lean_Parser_Tactic_grindTrace___closed__3;
    v___x_340_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_341_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_341_, 0, v___x_340_);
    lean_ctor_set(v___x_341_, 1, v___x_339_);
    lean_ctor_set(v___x_341_, 2, v___x_338_);
    return v___x_341_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__5() -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Parser_Tactic_grind___closed__13;
    v___x_343_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__4_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__4,
    );
    v___x_344_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_345_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_345_, 0, v___x_344_);
    lean_ctor_set(v___x_345_, 1, v___x_343_);
    lean_ctor_set(v___x_345_, 2, v___x_342_);
    return v___x_345_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__6() -> *mut LeanObject {
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v___x_346_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28_once),
        _init_l_Lean_Parser_Tactic_grind___closed__28,
    );
    v___x_347_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__5_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__5,
    );
    v___x_348_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_349_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_349_, 0, v___x_348_);
    lean_ctor_set(v___x_349_, 1, v___x_347_);
    lean_ctor_set(v___x_349_, 2, v___x_346_);
    return v___x_349_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace___closed__7() -> *mut LeanObject {
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    v___x_350_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__6_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__6,
    );
    v___x_351_ = lean_unsigned_to_nat(1022);
    v___x_352_ = l_Lean_Parser_Tactic_grindTrace___closed__1;
    v___x_353_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_353_, 0, v___x_352_);
    lean_ctor_set(v___x_353_, 1, v___x_351_);
    lean_ctor_set(v___x_353_, 2, v___x_350_);
    return v___x_353_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grindTrace() -> *mut LeanObject {
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    v___x_354_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grindTrace___closed__7_once),
        _init_l_Lean_Parser_Tactic_grindTrace___closed__7,
    );
    return v___x_354_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__3() -> *mut LeanObject {
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Lean_Parser_Tactic_optConfig;
    v___x_365_ = l_Lean_Parser_Tactic_sym___closed__2;
    v___x_366_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_367_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_367_, 0, v___x_366_);
    lean_ctor_set(v___x_367_, 1, v___x_365_);
    lean_ctor_set(v___x_367_, 2, v___x_364_);
    return v___x_367_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__4() -> *mut LeanObject {
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Lean_Parser_Tactic_grind___closed__13;
    v___x_369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__3_once),
        _init_l_Lean_Parser_Tactic_sym___closed__3,
    );
    v___x_370_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_371_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_371_, 0, v___x_370_);
    lean_ctor_set(v___x_371_, 1, v___x_369_);
    lean_ctor_set(v___x_371_, 2, v___x_368_);
    return v___x_371_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__5() -> *mut LeanObject {
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    v___x_372_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind___closed__28_once),
        _init_l_Lean_Parser_Tactic_grind___closed__28,
    );
    v___x_373_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__4_once),
        _init_l_Lean_Parser_Tactic_sym___closed__4,
    );
    v___x_374_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_375_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_375_, 0, v___x_374_);
    lean_ctor_set(v___x_375_, 1, v___x_373_);
    lean_ctor_set(v___x_375_, 2, v___x_372_);
    return v___x_375_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__6() -> *mut LeanObject {
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    v___x_376_ = l_Lean_Parser_Tactic_grind___closed__31;
    v___x_377_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__5_once),
        _init_l_Lean_Parser_Tactic_sym___closed__5,
    );
    v___x_378_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_379_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_379_, 0, v___x_378_);
    lean_ctor_set(v___x_379_, 1, v___x_377_);
    lean_ctor_set(v___x_379_, 2, v___x_376_);
    return v___x_379_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__7() -> *mut LeanObject {
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Parser_Tactic_Grind_grindSeq;
    v___x_381_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__6_once),
        _init_l_Lean_Parser_Tactic_sym___closed__6,
    );
    v___x_382_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_383_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_383_, 0, v___x_382_);
    lean_ctor_set(v___x_383_, 1, v___x_381_);
    lean_ctor_set(v___x_383_, 2, v___x_380_);
    return v___x_383_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym___closed__8() -> *mut LeanObject {
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    v___x_384_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__7_once),
        _init_l_Lean_Parser_Tactic_sym___closed__7,
    );
    v___x_385_ = lean_unsigned_to_nat(1022);
    v___x_386_ = l_Lean_Parser_Tactic_sym___closed__1;
    v___x_387_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_387_, 0, v___x_386_);
    lean_ctor_set(v___x_387_, 1, v___x_385_);
    lean_ctor_set(v___x_387_, 2, v___x_384_);
    return v___x_387_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_sym() -> *mut LeanObject {
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    v___x_388_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_sym___closed__8_once),
        _init_l_Lean_Parser_Tactic_sym___closed__8,
    );
    return v___x_388_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_cutsat___closed__3() -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = l_Lean_Parser_Tactic_optConfig;
    v___x_399_ = l_Lean_Parser_Tactic_cutsat___closed__2;
    v___x_400_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_401_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_401_, 0, v___x_400_);
    lean_ctor_set(v___x_401_, 1, v___x_399_);
    lean_ctor_set(v___x_401_, 2, v___x_398_);
    return v___x_401_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_cutsat___closed__4() -> *mut LeanObject {
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    v___x_402_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__3_once),
        _init_l_Lean_Parser_Tactic_cutsat___closed__3,
    );
    v___x_403_ = lean_unsigned_to_nat(1022);
    v___x_404_ = l_Lean_Parser_Tactic_cutsat___closed__1;
    v___x_405_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_405_, 0, v___x_404_);
    lean_ctor_set(v___x_405_, 1, v___x_403_);
    lean_ctor_set(v___x_405_, 2, v___x_402_);
    return v___x_405_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_cutsat() -> *mut LeanObject {
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    v___x_406_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_cutsat___closed__4_once),
        _init_l_Lean_Parser_Tactic_cutsat___closed__4,
    );
    return v___x_406_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_lia___closed__3() -> *mut LeanObject {
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    v___x_416_ = l_Lean_Parser_Tactic_optConfig;
    v___x_417_ = l_Lean_Parser_Tactic_lia___closed__2;
    v___x_418_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_419_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_419_, 0, v___x_418_);
    lean_ctor_set(v___x_419_, 1, v___x_417_);
    lean_ctor_set(v___x_419_, 2, v___x_416_);
    return v___x_419_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_lia___closed__4() -> *mut LeanObject {
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    v___x_420_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__3_once),
        _init_l_Lean_Parser_Tactic_lia___closed__3,
    );
    v___x_421_ = lean_unsigned_to_nat(1022);
    v___x_422_ = l_Lean_Parser_Tactic_lia___closed__1;
    v___x_423_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_423_, 0, v___x_422_);
    lean_ctor_set(v___x_423_, 1, v___x_421_);
    lean_ctor_set(v___x_423_, 2, v___x_420_);
    return v___x_423_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_lia() -> *mut LeanObject {
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    v___x_424_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_lia___closed__4_once),
        _init_l_Lean_Parser_Tactic_lia___closed__4,
    );
    return v___x_424_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__order___closed__3() -> *mut LeanObject {
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    v___x_434_ = l_Lean_Parser_Tactic_optConfig;
    v___x_435_ = l_Lean_Parser_Tactic_grind__order___closed__2;
    v___x_436_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_437_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_437_, 0, v___x_436_);
    lean_ctor_set(v___x_437_, 1, v___x_435_);
    lean_ctor_set(v___x_437_, 2, v___x_434_);
    return v___x_437_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__order___closed__4() -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__3_once),
        _init_l_Lean_Parser_Tactic_grind__order___closed__3,
    );
    v___x_439_ = lean_unsigned_to_nat(1022);
    v___x_440_ = l_Lean_Parser_Tactic_grind__order___closed__1;
    v___x_441_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_441_, 0, v___x_440_);
    lean_ctor_set(v___x_441_, 1, v___x_439_);
    lean_ctor_set(v___x_441_, 2, v___x_438_);
    return v___x_441_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__order() -> *mut LeanObject {
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    v___x_442_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__order___closed__4_once),
        _init_l_Lean_Parser_Tactic_grind__order___closed__4,
    );
    return v___x_442_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__linarith___closed__3() -> *mut LeanObject {
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    v___x_452_ = l_Lean_Parser_Tactic_optConfig;
    v___x_453_ = l_Lean_Parser_Tactic_grind__linarith___closed__2;
    v___x_454_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_455_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_455_, 0, v___x_454_);
    lean_ctor_set(v___x_455_, 1, v___x_453_);
    lean_ctor_set(v___x_455_, 2, v___x_452_);
    return v___x_455_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__linarith___closed__4() -> *mut LeanObject {
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    v___x_456_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__3_once),
        _init_l_Lean_Parser_Tactic_grind__linarith___closed__3,
    );
    v___x_457_ = lean_unsigned_to_nat(1022);
    v___x_458_ = l_Lean_Parser_Tactic_grind__linarith___closed__1;
    v___x_459_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_459_, 0, v___x_458_);
    lean_ctor_set(v___x_459_, 1, v___x_457_);
    lean_ctor_set(v___x_459_, 2, v___x_456_);
    return v___x_459_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grind__linarith() -> *mut LeanObject {
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    v___x_460_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grind__linarith___closed__4_once),
        _init_l_Lean_Parser_Tactic_grind__linarith___closed__4,
    );
    return v___x_460_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grobner___closed__3() -> *mut LeanObject {
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    v___x_470_ = l_Lean_Parser_Tactic_optConfig;
    v___x_471_ = l_Lean_Parser_Tactic_grobner___closed__2;
    v___x_472_ = l_Lean_Parser_Tactic_grind___closed__6;
    v___x_473_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_473_, 0, v___x_472_);
    lean_ctor_set(v___x_473_, 1, v___x_471_);
    lean_ctor_set(v___x_473_, 2, v___x_470_);
    return v___x_473_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grobner___closed__4() -> *mut LeanObject {
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    v___x_474_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__3_once),
        _init_l_Lean_Parser_Tactic_grobner___closed__3,
    );
    v___x_475_ = lean_unsigned_to_nat(1022);
    v___x_476_ = l_Lean_Parser_Tactic_grobner___closed__1;
    v___x_477_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_477_, 0, v___x_476_);
    lean_ctor_set(v___x_477_, 1, v___x_475_);
    lean_ctor_set(v___x_477_, 2, v___x_474_);
    return v___x_477_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_grobner() -> *mut LeanObject {
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    v___x_478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_grobner___closed__4_once),
        _init_l_Lean_Parser_Tactic_grobner___closed__4,
    );
    return v___x_478_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Tactics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Interactive(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Tactics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Tactic_grind = _init_l_Lean_Parser_Tactic_grind();
    lean_mark_persistent(l_Lean_Parser_Tactic_grind);
    l_Lean_Parser_Tactic_grindTrace = _init_l_Lean_Parser_Tactic_grindTrace();
    lean_mark_persistent(l_Lean_Parser_Tactic_grindTrace);
    l_Lean_Parser_Tactic_sym = _init_l_Lean_Parser_Tactic_sym();
    lean_mark_persistent(l_Lean_Parser_Tactic_sym);
    l_Lean_Parser_Tactic_cutsat = _init_l_Lean_Parser_Tactic_cutsat();
    lean_mark_persistent(l_Lean_Parser_Tactic_cutsat);
    l_Lean_Parser_Tactic_lia = _init_l_Lean_Parser_Tactic_lia();
    lean_mark_persistent(l_Lean_Parser_Tactic_lia);
    l_Lean_Parser_Tactic_grind__order = _init_l_Lean_Parser_Tactic_grind__order();
    lean_mark_persistent(l_Lean_Parser_Tactic_grind__order);
    l_Lean_Parser_Tactic_grind__linarith = _init_l_Lean_Parser_Tactic_grind__linarith();
    lean_mark_persistent(l_Lean_Parser_Tactic_grind__linarith);
    l_Lean_Parser_Tactic_grobner = _init_l_Lean_Parser_Tactic_grobner();
    lean_mark_persistent(l_Lean_Parser_Tactic_grobner);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Tactics(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Interactive(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Tactics(builtin);
}

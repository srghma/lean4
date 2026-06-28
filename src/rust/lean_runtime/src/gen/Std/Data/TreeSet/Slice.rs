// Lean compiler output
// Module: Std.Data.TreeSet.Slice
// Imports: Std.Data.TreeSet.Raw.Slice
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Std::Data::TreeSet::Raw::Slice::{
    initialize_Std_Data_TreeSet_Raw_Slice, runtime_initialize_Std_Data_TreeSet_Raw_Slice,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_string_utf8_byte_size,
};
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0_value:
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1_value:
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2_value:
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__3_value:
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5_value:
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__6_value:
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__8_value:
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__9_value:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__10_value:
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
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__10_value)
            as *mut crate::leanh::LeanObject,
        14997215300048349804 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14_value:
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
    m_data: [99, 111, 109, 112, 97, 114, 101, 0],
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__17_value:
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
        core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14_value)
            as *mut crate::leanh::LeanObject,
        16710690322389477741 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRiiSlice___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeSet_instSliceableRiiSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeSet_instSliceableRiiSlice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_toList__rii___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRicSlice___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRicSlice___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeSet_instSliceableRicSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeSet_instSliceableRicSlice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRicSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_toList__ric___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRioSlice___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRioSlice___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeSet_instSliceableRioSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeSet_instSliceableRioSlice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRioSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_toList__rio___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRciSlice___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRciSlice___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeSet_instSliceableRciSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeSet_instSliceableRciSlice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRciSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_toList__rci___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRcoSlice___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRcoSlice___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeSet_instSliceableRcoSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeSet_instSliceableRcoSlice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRcoSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_toList__rco___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRccSlice___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRccSlice___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeSet_instSliceableRccSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeSet_instSliceableRccSlice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRccSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_toList__rcc___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRoiSlice___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRoiSlice___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeSet_instSliceableRoiSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeSet_instSliceableRoiSlice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRoiSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_toList__roi___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRocSlice___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRocSlice___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeSet_instSliceableRocSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeSet_instSliceableRocSlice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRocSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_toList__roc___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRooSlice___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRooSlice___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_TreeSet_instSliceableRooSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_TreeSet_instSliceableRooSlice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRooSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_TreeSet_toList__roo___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_208_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__10;
    v___x_209_ = l_Lean_mkAtom(v___x_208_);
    return v___x_209_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_210_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12,
    );
    v___x_211_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5;
    v___x_212_ = lean_array_push(v___x_211_, v___x_210_);
    return v___x_212_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_214_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14;
    v___x_215_ = lean_string_utf8_byte_size(v___x_214_);
    return v___x_215_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_216_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15,
    );
    v___x_217_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_218_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14;
    v___x_219_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_219_, 0, v___x_218_);
    crate::leanh::lean_ctor_set(v___x_219_, 1, v___x_217_);
    crate::leanh::lean_ctor_set(v___x_219_, 2, v___x_216_);
    return v___x_219_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_222_ = crate::leanh::lean_box(0);
    v___x_223_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__17;
    v___x_224_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16,
    );
    v___x_225_ = crate::leanh::lean_box(2);
    v___x_226_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_226_, 0, v___x_225_);
    crate::leanh::lean_ctor_set(v___x_226_, 1, v___x_224_);
    crate::leanh::lean_ctor_set(v___x_226_, 2, v___x_223_);
    crate::leanh::lean_ctor_set(v___x_226_, 3, v___x_222_);
    return v___x_226_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_227_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18,
    );
    v___x_228_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13,
    );
    v___x_229_ = lean_array_push(v___x_228_, v___x_227_);
    return v___x_229_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_230_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19,
    );
    v___x_231_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11;
    v___x_232_ = crate::leanh::lean_box(2);
    v___x_233_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_233_, 0, v___x_232_);
    crate::leanh::lean_ctor_set(v___x_233_, 1, v___x_231_);
    crate::leanh::lean_ctor_set(v___x_233_, 2, v___x_230_);
    return v___x_233_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20,
    );
    v___x_235_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5;
    v___x_236_ = lean_array_push(v___x_235_, v___x_234_);
    return v___x_236_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_237_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21,
    );
    v___x_238_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__9;
    v___x_239_ = crate::leanh::lean_box(2);
    v___x_240_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_240_, 0, v___x_239_);
    crate::leanh::lean_ctor_set(v___x_240_, 1, v___x_238_);
    crate::leanh::lean_ctor_set(v___x_240_, 2, v___x_237_);
    return v___x_240_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_241_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22,
    );
    v___x_242_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5;
    v___x_243_ = lean_array_push(v___x_242_, v___x_241_);
    return v___x_243_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_244_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23,
    );
    v___x_245_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7;
    v___x_246_ = crate::leanh::lean_box(2);
    v___x_247_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_247_, 0, v___x_246_);
    crate::leanh::lean_ctor_set(v___x_247_, 1, v___x_245_);
    crate::leanh::lean_ctor_set(v___x_247_, 2, v___x_244_);
    return v___x_247_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_248_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24,
    );
    v___x_249_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5;
    v___x_250_ = lean_array_push(v___x_249_, v___x_248_);
    return v___x_250_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_251_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25,
    );
    v___x_252_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4;
    v___x_253_ = crate::leanh::lean_box(2);
    v___x_254_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_254_, 0, v___x_253_);
    crate::leanh::lean_ctor_set(v___x_254_, 1, v___x_252_);
    crate::leanh::lean_ctor_set(v___x_254_, 2, v___x_251_);
    return v___x_254_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_255_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_255_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRiiSlice___lam__0(
    mut v_carrier_256_: *mut crate::leanh::LeanObject,
    mut v_range_257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_258_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_258_, 0, v_carrier_256_);
    crate::leanh::lean_ctor_set(v___x_258_, 1, v_range_257_);
    return v___x_258_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRiiSlice(
    mut v_00_u03b1_260_: *mut crate::leanh::LeanObject,
    mut v_cmp_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_262_ = l_Std_TreeSet_instSliceableRiiSlice___closed__0;
    return v___f_262_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRiiSlice___boxed(
    mut v_00_u03b1_263_: *mut crate::leanh::LeanObject,
    mut v_cmp_264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_265_ = l_Std_TreeSet_instSliceableRiiSlice(v_00_u03b1_263_, v_cmp_264_);
    crate::leanh::lean_dec_ref(v_cmp_264_);
    return v_res_265_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__rii___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_266_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRicSlice___auto__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_267_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_267_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRicSlice___lam__0(
    mut v_carrier_268_: *mut crate::leanh::LeanObject,
    mut v_range_269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_270_, 0, v_carrier_268_);
    crate::leanh::lean_ctor_set(v___x_270_, 1, v_range_269_);
    return v___x_270_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRicSlice(
    mut v_00_u03b1_272_: *mut crate::leanh::LeanObject,
    mut v_cmp_273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_274_ = l_Std_TreeSet_instSliceableRicSlice___closed__0;
    return v___f_274_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRicSlice___boxed(
    mut v_00_u03b1_275_: *mut crate::leanh::LeanObject,
    mut v_cmp_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Std_TreeSet_instSliceableRicSlice(v_00_u03b1_275_, v_cmp_276_);
    crate::leanh::lean_dec_ref(v_cmp_276_);
    return v_res_277_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__ric___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_278_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_278_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRioSlice___auto__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_279_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_279_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRioSlice___lam__0(
    mut v_carrier_280_: *mut crate::leanh::LeanObject,
    mut v_range_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_282_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_282_, 0, v_carrier_280_);
    crate::leanh::lean_ctor_set(v___x_282_, 1, v_range_281_);
    return v___x_282_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRioSlice(
    mut v_00_u03b1_284_: *mut crate::leanh::LeanObject,
    mut v_cmp_285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_286_ = l_Std_TreeSet_instSliceableRioSlice___closed__0;
    return v___f_286_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRioSlice___boxed(
    mut v_00_u03b1_287_: *mut crate::leanh::LeanObject,
    mut v_cmp_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Std_TreeSet_instSliceableRioSlice(v_00_u03b1_287_, v_cmp_288_);
    crate::leanh::lean_dec_ref(v_cmp_288_);
    return v_res_289_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__rio___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_290_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_290_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRciSlice___auto__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_291_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRciSlice___lam__0(
    mut v_carrier_292_: *mut crate::leanh::LeanObject,
    mut v_range_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_294_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_294_, 0, v_carrier_292_);
    crate::leanh::lean_ctor_set(v___x_294_, 1, v_range_293_);
    return v___x_294_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRciSlice(
    mut v_00_u03b1_296_: *mut crate::leanh::LeanObject,
    mut v_cmp_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_298_ = l_Std_TreeSet_instSliceableRciSlice___closed__0;
    return v___f_298_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRciSlice___boxed(
    mut v_00_u03b1_299_: *mut crate::leanh::LeanObject,
    mut v_cmp_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_301_ = l_Std_TreeSet_instSliceableRciSlice(v_00_u03b1_299_, v_cmp_300_);
    crate::leanh::lean_dec_ref(v_cmp_300_);
    return v_res_301_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__rci___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_302_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_302_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRcoSlice___auto__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_303_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_303_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRcoSlice___lam__0(
    mut v_carrier_304_: *mut crate::leanh::LeanObject,
    mut v_range_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_306_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_306_, 0, v_carrier_304_);
    crate::leanh::lean_ctor_set(v___x_306_, 1, v_range_305_);
    return v___x_306_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRcoSlice(
    mut v_00_u03b1_308_: *mut crate::leanh::LeanObject,
    mut v_cmp_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_310_ = l_Std_TreeSet_instSliceableRcoSlice___closed__0;
    return v___f_310_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRcoSlice___boxed(
    mut v_00_u03b1_311_: *mut crate::leanh::LeanObject,
    mut v_cmp_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l_Std_TreeSet_instSliceableRcoSlice(v_00_u03b1_311_, v_cmp_312_);
    crate::leanh::lean_dec_ref(v_cmp_312_);
    return v_res_313_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__rco___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_314_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_314_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRccSlice___auto__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_315_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRccSlice___lam__0(
    mut v_carrier_316_: *mut crate::leanh::LeanObject,
    mut v_range_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_318_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_318_, 0, v_carrier_316_);
    crate::leanh::lean_ctor_set(v___x_318_, 1, v_range_317_);
    return v___x_318_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRccSlice(
    mut v_00_u03b1_320_: *mut crate::leanh::LeanObject,
    mut v_cmp_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_322_ = l_Std_TreeSet_instSliceableRccSlice___closed__0;
    return v___f_322_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRccSlice___boxed(
    mut v_00_u03b1_323_: *mut crate::leanh::LeanObject,
    mut v_cmp_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_325_ = l_Std_TreeSet_instSliceableRccSlice(v_00_u03b1_323_, v_cmp_324_);
    crate::leanh::lean_dec_ref(v_cmp_324_);
    return v_res_325_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__rcc___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_326_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_326_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRoiSlice___auto__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_327_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRoiSlice___lam__0(
    mut v_carrier_328_: *mut crate::leanh::LeanObject,
    mut v_range_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_330_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_330_, 0, v_carrier_328_);
    crate::leanh::lean_ctor_set(v___x_330_, 1, v_range_329_);
    return v___x_330_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRoiSlice(
    mut v_00_u03b1_332_: *mut crate::leanh::LeanObject,
    mut v_cmp_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_334_ = l_Std_TreeSet_instSliceableRoiSlice___closed__0;
    return v___f_334_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRoiSlice___boxed(
    mut v_00_u03b1_335_: *mut crate::leanh::LeanObject,
    mut v_cmp_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Std_TreeSet_instSliceableRoiSlice(v_00_u03b1_335_, v_cmp_336_);
    crate::leanh::lean_dec_ref(v_cmp_336_);
    return v_res_337_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__roi___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_338_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRocSlice___auto__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_339_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_339_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRocSlice___lam__0(
    mut v_carrier_340_: *mut crate::leanh::LeanObject,
    mut v_range_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_342_, 0, v_carrier_340_);
    crate::leanh::lean_ctor_set(v___x_342_, 1, v_range_341_);
    return v___x_342_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRocSlice(
    mut v_00_u03b1_344_: *mut crate::leanh::LeanObject,
    mut v_cmp_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_346_ = l_Std_TreeSet_instSliceableRocSlice___closed__0;
    return v___f_346_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRocSlice___boxed(
    mut v_00_u03b1_347_: *mut crate::leanh::LeanObject,
    mut v_cmp_348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_349_ = l_Std_TreeSet_instSliceableRocSlice(v_00_u03b1_347_, v_cmp_348_);
    crate::leanh::lean_dec_ref(v_cmp_348_);
    return v_res_349_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__roc___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_350_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRooSlice___auto__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_351_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_351_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRooSlice___lam__0(
    mut v_carrier_352_: *mut crate::leanh::LeanObject,
    mut v_range_353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_354_, 0, v_carrier_352_);
    crate::leanh::lean_ctor_set(v___x_354_, 1, v_range_353_);
    return v___x_354_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRooSlice(
    mut v_00_u03b1_356_: *mut crate::leanh::LeanObject,
    mut v_cmp_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_358_ = l_Std_TreeSet_instSliceableRooSlice___closed__0;
    return v___f_358_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRooSlice___boxed(
    mut v_00_u03b1_359_: *mut crate::leanh::LeanObject,
    mut v_cmp_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_361_ = l_Std_TreeSet_instSliceableRooSlice(v_00_u03b1_359_, v_cmp_360_);
    crate::leanh::lean_dec_ref(v_cmp_360_);
    return v_res_361_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__roo___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_362_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Slice(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeSet_Raw_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Slice(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_TreeSet_instSliceableRiiSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_instSliceableRiiSlice___auto__1);
    l_Std_TreeSet_toList__rii___auto__1 = _init_l_Std_TreeSet_toList__rii___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_toList__rii___auto__1);
    l_Std_TreeSet_instSliceableRicSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRicSlice___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_instSliceableRicSlice___auto__1);
    l_Std_TreeSet_toList__ric___auto__1 = _init_l_Std_TreeSet_toList__ric___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_toList__ric___auto__1);
    l_Std_TreeSet_instSliceableRioSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRioSlice___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_instSliceableRioSlice___auto__1);
    l_Std_TreeSet_toList__rio___auto__1 = _init_l_Std_TreeSet_toList__rio___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_toList__rio___auto__1);
    l_Std_TreeSet_instSliceableRciSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRciSlice___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_instSliceableRciSlice___auto__1);
    l_Std_TreeSet_toList__rci___auto__1 = _init_l_Std_TreeSet_toList__rci___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_toList__rci___auto__1);
    l_Std_TreeSet_instSliceableRcoSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRcoSlice___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_instSliceableRcoSlice___auto__1);
    l_Std_TreeSet_toList__rco___auto__1 = _init_l_Std_TreeSet_toList__rco___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_toList__rco___auto__1);
    l_Std_TreeSet_instSliceableRccSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRccSlice___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_instSliceableRccSlice___auto__1);
    l_Std_TreeSet_toList__rcc___auto__1 = _init_l_Std_TreeSet_toList__rcc___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_toList__rcc___auto__1);
    l_Std_TreeSet_instSliceableRoiSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRoiSlice___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_instSliceableRoiSlice___auto__1);
    l_Std_TreeSet_toList__roi___auto__1 = _init_l_Std_TreeSet_toList__roi___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_toList__roi___auto__1);
    l_Std_TreeSet_instSliceableRocSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRocSlice___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_instSliceableRocSlice___auto__1);
    l_Std_TreeSet_toList__roc___auto__1 = _init_l_Std_TreeSet_toList__roc___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_toList__roc___auto__1);
    l_Std_TreeSet_instSliceableRooSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRooSlice___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_instSliceableRooSlice___auto__1);
    l_Std_TreeSet_toList__roo___auto__1 = _init_l_Std_TreeSet_toList__roo___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_TreeSet_toList__roo___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeSet_Slice(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeSet_Raw_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Slice(builtin);
}

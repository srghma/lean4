// Lean compiler output
// Module: Std.Data.TreeMap.Slice
// Imports: Std.Data.TreeMap.Raw.Slice Std.Data.TreeMap.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Std::Data::TreeMap::Basic::{
    initialize_Std_Data_TreeMap_Basic, runtime_initialize_Std_Data_TreeMap_Basic,
};
use crate::r#gen::Std::Data::TreeMap::Raw::Slice::{
    initialize_Std_Data_TreeMap_Raw_Slice, runtime_initialize_Std_Data_TreeMap_Raw_Slice,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_unsigned_to_nat,
};
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1_value: LeanStringObject<7> =
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
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2_value: LeanStringObject<7> =
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
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__3_value: LeanStringObject<10> =
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
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__3_value)
        as *mut LeanObject;
static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
                l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
                l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value: LeanCtorObject<3> =
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
                l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__6_value: LeanStringObject<19> =
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
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__6_value)
        as *mut LeanObject;
static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
                l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
                l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value: LeanCtorObject<3> =
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
                l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__8_value: LeanStringObject<5> =
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
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__10_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__10_value)
        as *mut LeanObject;
static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
                l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
                l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value: LeanCtorObject<3> =
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
                l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11_value)
        as *mut LeanObject;
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14_value)
        as *mut LeanObject;
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14_value)
                as *mut LeanObject,
            16710690322389477741 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__17_value)
        as *mut LeanObject;
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeMap_instSliceableRiiSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRiiSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_instSliceableRiiSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_instSliceableRiiSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRiiSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_toList__rii___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap_instSliceableRicSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRicSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_instSliceableRicSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_instSliceableRicSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRicSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_toList__ric___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap_instSliceableRioSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRioSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_instSliceableRioSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_instSliceableRioSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRioSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_toList__rio___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap_instSliceableRciSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRciSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_instSliceableRciSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_instSliceableRciSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRciSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_toList__rci___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap_instSliceableRcoSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRcoSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_instSliceableRcoSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_instSliceableRcoSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRcoSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_toList__rco___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap_instSliceableRccSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRccSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_instSliceableRccSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_instSliceableRccSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRccSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_toList__rcc___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap_instSliceableRoiSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRoiSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_instSliceableRoiSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_instSliceableRoiSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRoiSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_toList__roi___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap_instSliceableRocSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRocSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_instSliceableRocSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_instSliceableRocSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRocSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_toList__roc___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeMap_instSliceableRooSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeMap_instSliceableRooSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeMap_instSliceableRooSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeMap_instSliceableRooSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeMap_instSliceableRooSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeMap_toList__roo___auto__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12() -> *mut LeanObject
{
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    v___x_226_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__10;
    v___x_227_ = l_Lean_mkAtom(v___x_226_);
    return v___x_227_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13() -> *mut LeanObject
{
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    v___x_228_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__12,
    );
    v___x_229_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5;
    v___x_230_ = lean_array_push(v___x_229_, v___x_228_);
    return v___x_230_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15() -> *mut LeanObject
{
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    v___x_232_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14;
    v___x_233_ = lean_string_utf8_byte_size(v___x_232_);
    return v___x_233_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16() -> *mut LeanObject
{
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    v___x_234_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__15,
    );
    v___x_235_ = lean_unsigned_to_nat(0);
    v___x_236_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__14;
    v___x_237_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_237_, 0, v___x_236_);
    lean_ctor_set(v___x_237_, 1, v___x_235_);
    lean_ctor_set(v___x_237_, 2, v___x_234_);
    return v___x_237_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18() -> *mut LeanObject
{
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    v___x_240_ = lean_box(0);
    v___x_241_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__17;
    v___x_242_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__16,
    );
    v___x_243_ = lean_box(2);
    v___x_244_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_244_, 0, v___x_243_);
    lean_ctor_set(v___x_244_, 1, v___x_242_);
    lean_ctor_set(v___x_244_, 2, v___x_241_);
    lean_ctor_set(v___x_244_, 3, v___x_240_);
    return v___x_244_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19() -> *mut LeanObject
{
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    v___x_245_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__18,
    );
    v___x_246_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__13,
    );
    v___x_247_ = lean_array_push(v___x_246_, v___x_245_);
    return v___x_247_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20() -> *mut LeanObject
{
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    v___x_248_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__19,
    );
    v___x_249_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__11;
    v___x_250_ = lean_box(2);
    v___x_251_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_251_, 0, v___x_250_);
    lean_ctor_set(v___x_251_, 1, v___x_249_);
    lean_ctor_set(v___x_251_, 2, v___x_248_);
    return v___x_251_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21() -> *mut LeanObject
{
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    v___x_252_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__20,
    );
    v___x_253_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5;
    v___x_254_ = lean_array_push(v___x_253_, v___x_252_);
    return v___x_254_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22() -> *mut LeanObject
{
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    v___x_255_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__21,
    );
    v___x_256_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__9;
    v___x_257_ = lean_box(2);
    v___x_258_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_258_, 0, v___x_257_);
    lean_ctor_set(v___x_258_, 1, v___x_256_);
    lean_ctor_set(v___x_258_, 2, v___x_255_);
    return v___x_258_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23() -> *mut LeanObject
{
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    v___x_259_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__22,
    );
    v___x_260_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5;
    v___x_261_ = lean_array_push(v___x_260_, v___x_259_);
    return v___x_261_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24() -> *mut LeanObject
{
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    v___x_262_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__23,
    );
    v___x_263_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__7;
    v___x_264_ = lean_box(2);
    v___x_265_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_265_, 0, v___x_264_);
    lean_ctor_set(v___x_265_, 1, v___x_263_);
    lean_ctor_set(v___x_265_, 2, v___x_262_);
    return v___x_265_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25() -> *mut LeanObject
{
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    v___x_266_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__24,
    );
    v___x_267_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__5;
    v___x_268_ = lean_array_push(v___x_267_, v___x_266_);
    return v___x_268_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26() -> *mut LeanObject
{
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v___x_269_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__25,
    );
    v___x_270_ = l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__4;
    v___x_271_ = lean_box(2);
    v___x_272_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_272_, 0, v___x_271_);
    lean_ctor_set(v___x_272_, 1, v___x_270_);
    lean_ctor_set(v___x_272_, 2, v___x_269_);
    return v___x_272_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1() -> *mut LeanObject {
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    v___x_273_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_273_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRiiSlice___lam__0(
    mut v_carrier_274_: *mut LeanObject,
    mut v_range_275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    v___x_276_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_276_, 0, v_carrier_274_);
    lean_ctor_set(v___x_276_, 1, v_range_275_);
    return v___x_276_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRiiSlice(
    mut v_00_u03b1_278_: *mut LeanObject,
    mut v_00_u03b2_279_: *mut LeanObject,
    mut v_cmp_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_281_: *mut LeanObject = core::ptr::null_mut();
    v___f_281_ = l_Std_TreeMap_instSliceableRiiSlice___closed__0;
    return v___f_281_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRiiSlice___boxed(
    mut v_00_u03b1_282_: *mut LeanObject,
    mut v_00_u03b2_283_: *mut LeanObject,
    mut v_cmp_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_285_: *mut LeanObject = core::ptr::null_mut();
    v_res_285_ = l_Std_TreeMap_instSliceableRiiSlice(v_00_u03b1_282_, v_00_u03b2_283_, v_cmp_284_);
    lean_dec_ref(v_cmp_284_);
    return v_res_285_;
}
pub unsafe fn _init_l_Std_TreeMap_toList__rii___auto__1() -> *mut LeanObject {
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    v___x_286_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_286_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRicSlice___auto__1() -> *mut LeanObject {
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    v___x_287_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_287_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRicSlice___lam__0(
    mut v_carrier_288_: *mut LeanObject,
    mut v_range_289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    v___x_290_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_290_, 0, v_carrier_288_);
    lean_ctor_set(v___x_290_, 1, v_range_289_);
    return v___x_290_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRicSlice(
    mut v_00_u03b1_292_: *mut LeanObject,
    mut v_00_u03b2_293_: *mut LeanObject,
    mut v_cmp_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_295_: *mut LeanObject = core::ptr::null_mut();
    v___f_295_ = l_Std_TreeMap_instSliceableRicSlice___closed__0;
    return v___f_295_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRicSlice___boxed(
    mut v_00_u03b1_296_: *mut LeanObject,
    mut v_00_u03b2_297_: *mut LeanObject,
    mut v_cmp_298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_299_: *mut LeanObject = core::ptr::null_mut();
    v_res_299_ = l_Std_TreeMap_instSliceableRicSlice(v_00_u03b1_296_, v_00_u03b2_297_, v_cmp_298_);
    lean_dec_ref(v_cmp_298_);
    return v_res_299_;
}
pub unsafe fn _init_l_Std_TreeMap_toList__ric___auto__1() -> *mut LeanObject {
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    v___x_300_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_300_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRioSlice___auto__1() -> *mut LeanObject {
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    v___x_301_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_301_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRioSlice___lam__0(
    mut v_carrier_302_: *mut LeanObject,
    mut v_range_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    v___x_304_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_304_, 0, v_carrier_302_);
    lean_ctor_set(v___x_304_, 1, v_range_303_);
    return v___x_304_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRioSlice(
    mut v_00_u03b1_306_: *mut LeanObject,
    mut v_00_u03b2_307_: *mut LeanObject,
    mut v_cmp_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_309_: *mut LeanObject = core::ptr::null_mut();
    v___f_309_ = l_Std_TreeMap_instSliceableRioSlice___closed__0;
    return v___f_309_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRioSlice___boxed(
    mut v_00_u03b1_310_: *mut LeanObject,
    mut v_00_u03b2_311_: *mut LeanObject,
    mut v_cmp_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_313_: *mut LeanObject = core::ptr::null_mut();
    v_res_313_ = l_Std_TreeMap_instSliceableRioSlice(v_00_u03b1_310_, v_00_u03b2_311_, v_cmp_312_);
    lean_dec_ref(v_cmp_312_);
    return v_res_313_;
}
pub unsafe fn _init_l_Std_TreeMap_toList__rio___auto__1() -> *mut LeanObject {
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    v___x_314_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_314_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRciSlice___auto__1() -> *mut LeanObject {
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    v___x_315_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_315_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRciSlice___lam__0(
    mut v_carrier_316_: *mut LeanObject,
    mut v_range_317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    v___x_318_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_318_, 0, v_carrier_316_);
    lean_ctor_set(v___x_318_, 1, v_range_317_);
    return v___x_318_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRciSlice(
    mut v_00_u03b1_320_: *mut LeanObject,
    mut v_00_u03b2_321_: *mut LeanObject,
    mut v_cmp_322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_323_: *mut LeanObject = core::ptr::null_mut();
    v___f_323_ = l_Std_TreeMap_instSliceableRciSlice___closed__0;
    return v___f_323_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRciSlice___boxed(
    mut v_00_u03b1_324_: *mut LeanObject,
    mut v_00_u03b2_325_: *mut LeanObject,
    mut v_cmp_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_327_: *mut LeanObject = core::ptr::null_mut();
    v_res_327_ = l_Std_TreeMap_instSliceableRciSlice(v_00_u03b1_324_, v_00_u03b2_325_, v_cmp_326_);
    lean_dec_ref(v_cmp_326_);
    return v_res_327_;
}
pub unsafe fn _init_l_Std_TreeMap_toList__rci___auto__1() -> *mut LeanObject {
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    v___x_328_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_328_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRcoSlice___auto__1() -> *mut LeanObject {
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    v___x_329_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_329_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRcoSlice___lam__0(
    mut v_carrier_330_: *mut LeanObject,
    mut v_range_331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    v___x_332_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_332_, 0, v_carrier_330_);
    lean_ctor_set(v___x_332_, 1, v_range_331_);
    return v___x_332_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRcoSlice(
    mut v_00_u03b1_334_: *mut LeanObject,
    mut v_00_u03b2_335_: *mut LeanObject,
    mut v_cmp_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_337_: *mut LeanObject = core::ptr::null_mut();
    v___f_337_ = l_Std_TreeMap_instSliceableRcoSlice___closed__0;
    return v___f_337_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRcoSlice___boxed(
    mut v_00_u03b1_338_: *mut LeanObject,
    mut v_00_u03b2_339_: *mut LeanObject,
    mut v_cmp_340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_341_: *mut LeanObject = core::ptr::null_mut();
    v_res_341_ = l_Std_TreeMap_instSliceableRcoSlice(v_00_u03b1_338_, v_00_u03b2_339_, v_cmp_340_);
    lean_dec_ref(v_cmp_340_);
    return v_res_341_;
}
pub unsafe fn _init_l_Std_TreeMap_toList__rco___auto__1() -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_342_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRccSlice___auto__1() -> *mut LeanObject {
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    v___x_343_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_343_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRccSlice___lam__0(
    mut v_carrier_344_: *mut LeanObject,
    mut v_range_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    v___x_346_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_346_, 0, v_carrier_344_);
    lean_ctor_set(v___x_346_, 1, v_range_345_);
    return v___x_346_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRccSlice(
    mut v_00_u03b1_348_: *mut LeanObject,
    mut v_00_u03b2_349_: *mut LeanObject,
    mut v_cmp_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_351_: *mut LeanObject = core::ptr::null_mut();
    v___f_351_ = l_Std_TreeMap_instSliceableRccSlice___closed__0;
    return v___f_351_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRccSlice___boxed(
    mut v_00_u03b1_352_: *mut LeanObject,
    mut v_00_u03b2_353_: *mut LeanObject,
    mut v_cmp_354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_355_: *mut LeanObject = core::ptr::null_mut();
    v_res_355_ = l_Std_TreeMap_instSliceableRccSlice(v_00_u03b1_352_, v_00_u03b2_353_, v_cmp_354_);
    lean_dec_ref(v_cmp_354_);
    return v_res_355_;
}
pub unsafe fn _init_l_Std_TreeMap_toList__rcc___auto__1() -> *mut LeanObject {
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    v___x_356_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_356_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRoiSlice___auto__1() -> *mut LeanObject {
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    v___x_357_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_357_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRoiSlice___lam__0(
    mut v_carrier_358_: *mut LeanObject,
    mut v_range_359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    v___x_360_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_360_, 0, v_carrier_358_);
    lean_ctor_set(v___x_360_, 1, v_range_359_);
    return v___x_360_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRoiSlice(
    mut v_00_u03b1_362_: *mut LeanObject,
    mut v_00_u03b2_363_: *mut LeanObject,
    mut v_cmp_364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_365_: *mut LeanObject = core::ptr::null_mut();
    v___f_365_ = l_Std_TreeMap_instSliceableRoiSlice___closed__0;
    return v___f_365_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRoiSlice___boxed(
    mut v_00_u03b1_366_: *mut LeanObject,
    mut v_00_u03b2_367_: *mut LeanObject,
    mut v_cmp_368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_369_: *mut LeanObject = core::ptr::null_mut();
    v_res_369_ = l_Std_TreeMap_instSliceableRoiSlice(v_00_u03b1_366_, v_00_u03b2_367_, v_cmp_368_);
    lean_dec_ref(v_cmp_368_);
    return v_res_369_;
}
pub unsafe fn _init_l_Std_TreeMap_toList__roi___auto__1() -> *mut LeanObject {
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    v___x_370_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_370_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRocSlice___auto__1() -> *mut LeanObject {
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    v___x_371_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_371_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRocSlice___lam__0(
    mut v_carrier_372_: *mut LeanObject,
    mut v_range_373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    v___x_374_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_374_, 0, v_carrier_372_);
    lean_ctor_set(v___x_374_, 1, v_range_373_);
    return v___x_374_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRocSlice(
    mut v_00_u03b1_376_: *mut LeanObject,
    mut v_00_u03b2_377_: *mut LeanObject,
    mut v_cmp_378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_379_: *mut LeanObject = core::ptr::null_mut();
    v___f_379_ = l_Std_TreeMap_instSliceableRocSlice___closed__0;
    return v___f_379_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRocSlice___boxed(
    mut v_00_u03b1_380_: *mut LeanObject,
    mut v_00_u03b2_381_: *mut LeanObject,
    mut v_cmp_382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_383_: *mut LeanObject = core::ptr::null_mut();
    v_res_383_ = l_Std_TreeMap_instSliceableRocSlice(v_00_u03b1_380_, v_00_u03b2_381_, v_cmp_382_);
    lean_dec_ref(v_cmp_382_);
    return v_res_383_;
}
pub unsafe fn _init_l_Std_TreeMap_toList__roc___auto__1() -> *mut LeanObject {
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    v___x_384_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_384_;
}
pub unsafe fn _init_l_Std_TreeMap_instSliceableRooSlice___auto__1() -> *mut LeanObject {
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    v___x_385_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_385_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRooSlice___lam__0(
    mut v_carrier_386_: *mut LeanObject,
    mut v_range_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    v___x_388_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_388_, 0, v_carrier_386_);
    lean_ctor_set(v___x_388_, 1, v_range_387_);
    return v___x_388_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRooSlice(
    mut v_00_u03b1_390_: *mut LeanObject,
    mut v_00_u03b2_391_: *mut LeanObject,
    mut v_cmp_392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_393_: *mut LeanObject = core::ptr::null_mut();
    v___f_393_ = l_Std_TreeMap_instSliceableRooSlice___closed__0;
    return v___f_393_;
}
pub unsafe fn l_Std_TreeMap_instSliceableRooSlice___boxed(
    mut v_00_u03b1_394_: *mut LeanObject,
    mut v_00_u03b2_395_: *mut LeanObject,
    mut v_cmp_396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_397_: *mut LeanObject = core::ptr::null_mut();
    v_res_397_ = l_Std_TreeMap_instSliceableRooSlice(v_00_u03b1_394_, v_00_u03b2_395_, v_cmp_396_);
    lean_dec_ref(v_cmp_396_);
    return v_res_397_;
}
pub unsafe fn _init_l_Std_TreeMap_toList__roo___auto__1() -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_398_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_Slice(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Raw_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeMap_Slice(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_TreeMap_instSliceableRiiSlice___auto__1 =
        _init_l_Std_TreeMap_instSliceableRiiSlice___auto__1();
    lean_mark_persistent(l_Std_TreeMap_instSliceableRiiSlice___auto__1);
    l_Std_TreeMap_toList__rii___auto__1 = _init_l_Std_TreeMap_toList__rii___auto__1();
    lean_mark_persistent(l_Std_TreeMap_toList__rii___auto__1);
    l_Std_TreeMap_instSliceableRicSlice___auto__1 =
        _init_l_Std_TreeMap_instSliceableRicSlice___auto__1();
    lean_mark_persistent(l_Std_TreeMap_instSliceableRicSlice___auto__1);
    l_Std_TreeMap_toList__ric___auto__1 = _init_l_Std_TreeMap_toList__ric___auto__1();
    lean_mark_persistent(l_Std_TreeMap_toList__ric___auto__1);
    l_Std_TreeMap_instSliceableRioSlice___auto__1 =
        _init_l_Std_TreeMap_instSliceableRioSlice___auto__1();
    lean_mark_persistent(l_Std_TreeMap_instSliceableRioSlice___auto__1);
    l_Std_TreeMap_toList__rio___auto__1 = _init_l_Std_TreeMap_toList__rio___auto__1();
    lean_mark_persistent(l_Std_TreeMap_toList__rio___auto__1);
    l_Std_TreeMap_instSliceableRciSlice___auto__1 =
        _init_l_Std_TreeMap_instSliceableRciSlice___auto__1();
    lean_mark_persistent(l_Std_TreeMap_instSliceableRciSlice___auto__1);
    l_Std_TreeMap_toList__rci___auto__1 = _init_l_Std_TreeMap_toList__rci___auto__1();
    lean_mark_persistent(l_Std_TreeMap_toList__rci___auto__1);
    l_Std_TreeMap_instSliceableRcoSlice___auto__1 =
        _init_l_Std_TreeMap_instSliceableRcoSlice___auto__1();
    lean_mark_persistent(l_Std_TreeMap_instSliceableRcoSlice___auto__1);
    l_Std_TreeMap_toList__rco___auto__1 = _init_l_Std_TreeMap_toList__rco___auto__1();
    lean_mark_persistent(l_Std_TreeMap_toList__rco___auto__1);
    l_Std_TreeMap_instSliceableRccSlice___auto__1 =
        _init_l_Std_TreeMap_instSliceableRccSlice___auto__1();
    lean_mark_persistent(l_Std_TreeMap_instSliceableRccSlice___auto__1);
    l_Std_TreeMap_toList__rcc___auto__1 = _init_l_Std_TreeMap_toList__rcc___auto__1();
    lean_mark_persistent(l_Std_TreeMap_toList__rcc___auto__1);
    l_Std_TreeMap_instSliceableRoiSlice___auto__1 =
        _init_l_Std_TreeMap_instSliceableRoiSlice___auto__1();
    lean_mark_persistent(l_Std_TreeMap_instSliceableRoiSlice___auto__1);
    l_Std_TreeMap_toList__roi___auto__1 = _init_l_Std_TreeMap_toList__roi___auto__1();
    lean_mark_persistent(l_Std_TreeMap_toList__roi___auto__1);
    l_Std_TreeMap_instSliceableRocSlice___auto__1 =
        _init_l_Std_TreeMap_instSliceableRocSlice___auto__1();
    lean_mark_persistent(l_Std_TreeMap_instSliceableRocSlice___auto__1);
    l_Std_TreeMap_toList__roc___auto__1 = _init_l_Std_TreeMap_toList__roc___auto__1();
    lean_mark_persistent(l_Std_TreeMap_toList__roc___auto__1);
    l_Std_TreeMap_instSliceableRooSlice___auto__1 =
        _init_l_Std_TreeMap_instSliceableRooSlice___auto__1();
    lean_mark_persistent(l_Std_TreeMap_instSliceableRooSlice___auto__1);
    l_Std_TreeMap_toList__roo___auto__1 = _init_l_Std_TreeMap_toList__roo___auto__1();
    lean_mark_persistent(l_Std_TreeMap_toList__roo___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeMap_Slice(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Raw_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_Slice(builtin);
}

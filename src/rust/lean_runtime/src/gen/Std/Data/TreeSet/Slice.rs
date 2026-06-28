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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_unsigned_to_nat,
};
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1_value: LeanStringObject<7> =
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2_value: LeanStringObject<7> =
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__3_value: LeanStringObject<10> =
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__3_value)
        as *mut LeanObject;
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
                l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
                l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value: LeanCtorObject<3> =
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
                l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__6_value: LeanStringObject<19> =
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__6_value)
        as *mut LeanObject;
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
                l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
                l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value: LeanCtorObject<3> =
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
                l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__8_value: LeanStringObject<5> =
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__10_value: LeanStringObject<6> =
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__10_value)
        as *mut LeanObject;
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
                l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
                l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value: LeanCtorObject<3> =
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
                l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11_value)
        as *mut LeanObject;
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14_value: LeanStringObject<8> =
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
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14_value)
        as *mut LeanObject;
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14_value)
                as *mut LeanObject,
            16710690322389477741 as *mut LeanObject,
        ],
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__17_value)
        as *mut LeanObject;
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRiiSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRiiSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_instSliceableRiiSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_instSliceableRiiSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRiiSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_toList__rii___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRicSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRicSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_instSliceableRicSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_instSliceableRicSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRicSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_toList__ric___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRioSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRioSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_instSliceableRioSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_instSliceableRioSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRioSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_toList__rio___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRciSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRciSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_instSliceableRciSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_instSliceableRciSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRciSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_toList__rci___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRcoSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRcoSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_instSliceableRcoSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_instSliceableRcoSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRcoSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_toList__rco___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRccSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRccSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_instSliceableRccSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_instSliceableRccSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRccSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_toList__rcc___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRoiSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRoiSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_instSliceableRoiSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_instSliceableRoiSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRoiSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_toList__roi___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRocSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRocSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_instSliceableRocSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_instSliceableRocSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRocSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_toList__roc___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_TreeSet_instSliceableRooSlice___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_TreeSet_instSliceableRooSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_TreeSet_instSliceableRooSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_TreeSet_instSliceableRooSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_TreeSet_instSliceableRooSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Std_TreeSet_toList__roo___auto__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12() -> *mut LeanObject
{
    let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
    v___x_208_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__10;
    v___x_209_ = l_Lean_mkAtom(v___x_208_);
    return v___x_209_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13() -> *mut LeanObject
{
    let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    v___x_210_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__12,
    );
    v___x_211_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5;
    v___x_212_ = lean_array_push(v___x_211_, v___x_210_);
    return v___x_212_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15() -> *mut LeanObject
{
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    v___x_214_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14;
    v___x_215_ = lean_string_utf8_byte_size(v___x_214_);
    return v___x_215_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16() -> *mut LeanObject
{
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    v___x_216_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__15,
    );
    v___x_217_ = lean_unsigned_to_nat(0);
    v___x_218_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__14;
    v___x_219_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_219_, 0, v___x_218_);
    lean_ctor_set(v___x_219_, 1, v___x_217_);
    lean_ctor_set(v___x_219_, 2, v___x_216_);
    return v___x_219_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18() -> *mut LeanObject
{
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    v___x_222_ = lean_box(0);
    v___x_223_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__17;
    v___x_224_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__16,
    );
    v___x_225_ = lean_box(2);
    v___x_226_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_226_, 0, v___x_225_);
    lean_ctor_set(v___x_226_, 1, v___x_224_);
    lean_ctor_set(v___x_226_, 2, v___x_223_);
    lean_ctor_set(v___x_226_, 3, v___x_222_);
    return v___x_226_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19() -> *mut LeanObject
{
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    v___x_227_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__18,
    );
    v___x_228_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__13,
    );
    v___x_229_ = lean_array_push(v___x_228_, v___x_227_);
    return v___x_229_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20() -> *mut LeanObject
{
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    v___x_230_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__19,
    );
    v___x_231_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__11;
    v___x_232_ = lean_box(2);
    v___x_233_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_233_, 0, v___x_232_);
    lean_ctor_set(v___x_233_, 1, v___x_231_);
    lean_ctor_set(v___x_233_, 2, v___x_230_);
    return v___x_233_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21() -> *mut LeanObject
{
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    v___x_234_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__20,
    );
    v___x_235_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5;
    v___x_236_ = lean_array_push(v___x_235_, v___x_234_);
    return v___x_236_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22() -> *mut LeanObject
{
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    v___x_237_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__21,
    );
    v___x_238_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__9;
    v___x_239_ = lean_box(2);
    v___x_240_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_240_, 0, v___x_239_);
    lean_ctor_set(v___x_240_, 1, v___x_238_);
    lean_ctor_set(v___x_240_, 2, v___x_237_);
    return v___x_240_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23() -> *mut LeanObject
{
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    v___x_241_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__22,
    );
    v___x_242_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5;
    v___x_243_ = lean_array_push(v___x_242_, v___x_241_);
    return v___x_243_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24() -> *mut LeanObject
{
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    v___x_244_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__23,
    );
    v___x_245_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__7;
    v___x_246_ = lean_box(2);
    v___x_247_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_247_, 0, v___x_246_);
    lean_ctor_set(v___x_247_, 1, v___x_245_);
    lean_ctor_set(v___x_247_, 2, v___x_244_);
    return v___x_247_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25() -> *mut LeanObject
{
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    v___x_248_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__24,
    );
    v___x_249_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__5;
    v___x_250_ = lean_array_push(v___x_249_, v___x_248_);
    return v___x_250_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26() -> *mut LeanObject
{
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    v___x_251_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__25,
    );
    v___x_252_ = l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__4;
    v___x_253_ = lean_box(2);
    v___x_254_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_254_, 0, v___x_253_);
    lean_ctor_set(v___x_254_, 1, v___x_252_);
    lean_ctor_set(v___x_254_, 2, v___x_251_);
    return v___x_254_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1() -> *mut LeanObject {
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    v___x_255_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_255_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRiiSlice___lam__0(
    mut v_carrier_256_: *mut LeanObject,
    mut v_range_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    v___x_258_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_258_, 0, v_carrier_256_);
    lean_ctor_set(v___x_258_, 1, v_range_257_);
    return v___x_258_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRiiSlice(
    mut v_00_u03b1_260_: *mut LeanObject,
    mut v_cmp_261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_262_: *mut LeanObject = core::ptr::null_mut();
    v___f_262_ = l_Std_TreeSet_instSliceableRiiSlice___closed__0;
    return v___f_262_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRiiSlice___boxed(
    mut v_00_u03b1_263_: *mut LeanObject,
    mut v_cmp_264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_265_: *mut LeanObject = core::ptr::null_mut();
    v_res_265_ = l_Std_TreeSet_instSliceableRiiSlice(v_00_u03b1_263_, v_cmp_264_);
    lean_dec_ref(v_cmp_264_);
    return v_res_265_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__rii___auto__1() -> *mut LeanObject {
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    v___x_266_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_266_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRicSlice___auto__1() -> *mut LeanObject {
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    v___x_267_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_267_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRicSlice___lam__0(
    mut v_carrier_268_: *mut LeanObject,
    mut v_range_269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    v___x_270_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_270_, 0, v_carrier_268_);
    lean_ctor_set(v___x_270_, 1, v_range_269_);
    return v___x_270_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRicSlice(
    mut v_00_u03b1_272_: *mut LeanObject,
    mut v_cmp_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_274_: *mut LeanObject = core::ptr::null_mut();
    v___f_274_ = l_Std_TreeSet_instSliceableRicSlice___closed__0;
    return v___f_274_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRicSlice___boxed(
    mut v_00_u03b1_275_: *mut LeanObject,
    mut v_cmp_276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_277_: *mut LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Std_TreeSet_instSliceableRicSlice(v_00_u03b1_275_, v_cmp_276_);
    lean_dec_ref(v_cmp_276_);
    return v_res_277_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__ric___auto__1() -> *mut LeanObject {
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    v___x_278_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_278_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRioSlice___auto__1() -> *mut LeanObject {
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    v___x_279_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_279_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRioSlice___lam__0(
    mut v_carrier_280_: *mut LeanObject,
    mut v_range_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    v___x_282_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_282_, 0, v_carrier_280_);
    lean_ctor_set(v___x_282_, 1, v_range_281_);
    return v___x_282_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRioSlice(
    mut v_00_u03b1_284_: *mut LeanObject,
    mut v_cmp_285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_286_: *mut LeanObject = core::ptr::null_mut();
    v___f_286_ = l_Std_TreeSet_instSliceableRioSlice___closed__0;
    return v___f_286_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRioSlice___boxed(
    mut v_00_u03b1_287_: *mut LeanObject,
    mut v_cmp_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_289_: *mut LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Std_TreeSet_instSliceableRioSlice(v_00_u03b1_287_, v_cmp_288_);
    lean_dec_ref(v_cmp_288_);
    return v_res_289_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__rio___auto__1() -> *mut LeanObject {
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    v___x_290_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_290_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRciSlice___auto__1() -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    v___x_291_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_291_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRciSlice___lam__0(
    mut v_carrier_292_: *mut LeanObject,
    mut v_range_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    v___x_294_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_294_, 0, v_carrier_292_);
    lean_ctor_set(v___x_294_, 1, v_range_293_);
    return v___x_294_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRciSlice(
    mut v_00_u03b1_296_: *mut LeanObject,
    mut v_cmp_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_298_: *mut LeanObject = core::ptr::null_mut();
    v___f_298_ = l_Std_TreeSet_instSliceableRciSlice___closed__0;
    return v___f_298_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRciSlice___boxed(
    mut v_00_u03b1_299_: *mut LeanObject,
    mut v_cmp_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_301_: *mut LeanObject = core::ptr::null_mut();
    v_res_301_ = l_Std_TreeSet_instSliceableRciSlice(v_00_u03b1_299_, v_cmp_300_);
    lean_dec_ref(v_cmp_300_);
    return v_res_301_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__rci___auto__1() -> *mut LeanObject {
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    v___x_302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_302_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRcoSlice___auto__1() -> *mut LeanObject {
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    v___x_303_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_303_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRcoSlice___lam__0(
    mut v_carrier_304_: *mut LeanObject,
    mut v_range_305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    v___x_306_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_306_, 0, v_carrier_304_);
    lean_ctor_set(v___x_306_, 1, v_range_305_);
    return v___x_306_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRcoSlice(
    mut v_00_u03b1_308_: *mut LeanObject,
    mut v_cmp_309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_310_: *mut LeanObject = core::ptr::null_mut();
    v___f_310_ = l_Std_TreeSet_instSliceableRcoSlice___closed__0;
    return v___f_310_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRcoSlice___boxed(
    mut v_00_u03b1_311_: *mut LeanObject,
    mut v_cmp_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_313_: *mut LeanObject = core::ptr::null_mut();
    v_res_313_ = l_Std_TreeSet_instSliceableRcoSlice(v_00_u03b1_311_, v_cmp_312_);
    lean_dec_ref(v_cmp_312_);
    return v_res_313_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__rco___auto__1() -> *mut LeanObject {
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    v___x_314_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_314_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRccSlice___auto__1() -> *mut LeanObject {
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    v___x_315_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_315_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRccSlice___lam__0(
    mut v_carrier_316_: *mut LeanObject,
    mut v_range_317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    v___x_318_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_318_, 0, v_carrier_316_);
    lean_ctor_set(v___x_318_, 1, v_range_317_);
    return v___x_318_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRccSlice(
    mut v_00_u03b1_320_: *mut LeanObject,
    mut v_cmp_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_322_: *mut LeanObject = core::ptr::null_mut();
    v___f_322_ = l_Std_TreeSet_instSliceableRccSlice___closed__0;
    return v___f_322_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRccSlice___boxed(
    mut v_00_u03b1_323_: *mut LeanObject,
    mut v_cmp_324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_325_: *mut LeanObject = core::ptr::null_mut();
    v_res_325_ = l_Std_TreeSet_instSliceableRccSlice(v_00_u03b1_323_, v_cmp_324_);
    lean_dec_ref(v_cmp_324_);
    return v_res_325_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__rcc___auto__1() -> *mut LeanObject {
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    v___x_326_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_326_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRoiSlice___auto__1() -> *mut LeanObject {
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    v___x_327_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_327_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRoiSlice___lam__0(
    mut v_carrier_328_: *mut LeanObject,
    mut v_range_329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    v___x_330_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_330_, 0, v_carrier_328_);
    lean_ctor_set(v___x_330_, 1, v_range_329_);
    return v___x_330_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRoiSlice(
    mut v_00_u03b1_332_: *mut LeanObject,
    mut v_cmp_333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_334_: *mut LeanObject = core::ptr::null_mut();
    v___f_334_ = l_Std_TreeSet_instSliceableRoiSlice___closed__0;
    return v___f_334_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRoiSlice___boxed(
    mut v_00_u03b1_335_: *mut LeanObject,
    mut v_cmp_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_337_: *mut LeanObject = core::ptr::null_mut();
    v_res_337_ = l_Std_TreeSet_instSliceableRoiSlice(v_00_u03b1_335_, v_cmp_336_);
    lean_dec_ref(v_cmp_336_);
    return v_res_337_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__roi___auto__1() -> *mut LeanObject {
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    v___x_338_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_338_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRocSlice___auto__1() -> *mut LeanObject {
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    v___x_339_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_339_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRocSlice___lam__0(
    mut v_carrier_340_: *mut LeanObject,
    mut v_range_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_342_, 0, v_carrier_340_);
    lean_ctor_set(v___x_342_, 1, v_range_341_);
    return v___x_342_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRocSlice(
    mut v_00_u03b1_344_: *mut LeanObject,
    mut v_cmp_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_346_: *mut LeanObject = core::ptr::null_mut();
    v___f_346_ = l_Std_TreeSet_instSliceableRocSlice___closed__0;
    return v___f_346_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRocSlice___boxed(
    mut v_00_u03b1_347_: *mut LeanObject,
    mut v_cmp_348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_349_: *mut LeanObject = core::ptr::null_mut();
    v_res_349_ = l_Std_TreeSet_instSliceableRocSlice(v_00_u03b1_347_, v_cmp_348_);
    lean_dec_ref(v_cmp_348_);
    return v_res_349_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__roc___auto__1() -> *mut LeanObject {
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    v___x_350_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_350_;
}
pub unsafe fn _init_l_Std_TreeSet_instSliceableRooSlice___auto__1() -> *mut LeanObject {
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    v___x_351_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_351_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRooSlice___lam__0(
    mut v_carrier_352_: *mut LeanObject,
    mut v_range_353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    v___x_354_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_354_, 0, v_carrier_352_);
    lean_ctor_set(v___x_354_, 1, v_range_353_);
    return v___x_354_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRooSlice(
    mut v_00_u03b1_356_: *mut LeanObject,
    mut v_cmp_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_358_: *mut LeanObject = core::ptr::null_mut();
    v___f_358_ = l_Std_TreeSet_instSliceableRooSlice___closed__0;
    return v___f_358_;
}
pub unsafe fn l_Std_TreeSet_instSliceableRooSlice___boxed(
    mut v_00_u03b1_359_: *mut LeanObject,
    mut v_cmp_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_361_: *mut LeanObject = core::ptr::null_mut();
    v_res_361_ = l_Std_TreeSet_instSliceableRooSlice(v_00_u03b1_359_, v_cmp_360_);
    lean_dec_ref(v_cmp_360_);
    return v_res_361_;
}
pub unsafe fn _init_l_Std_TreeSet_toList__roo___auto__1() -> *mut LeanObject {
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    v___x_362_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26_once),
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1___closed__26,
    );
    return v___x_362_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Slice(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeSet_Raw_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Slice(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_TreeSet_instSliceableRiiSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRiiSlice___auto__1();
    lean_mark_persistent(l_Std_TreeSet_instSliceableRiiSlice___auto__1);
    l_Std_TreeSet_toList__rii___auto__1 = _init_l_Std_TreeSet_toList__rii___auto__1();
    lean_mark_persistent(l_Std_TreeSet_toList__rii___auto__1);
    l_Std_TreeSet_instSliceableRicSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRicSlice___auto__1();
    lean_mark_persistent(l_Std_TreeSet_instSliceableRicSlice___auto__1);
    l_Std_TreeSet_toList__ric___auto__1 = _init_l_Std_TreeSet_toList__ric___auto__1();
    lean_mark_persistent(l_Std_TreeSet_toList__ric___auto__1);
    l_Std_TreeSet_instSliceableRioSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRioSlice___auto__1();
    lean_mark_persistent(l_Std_TreeSet_instSliceableRioSlice___auto__1);
    l_Std_TreeSet_toList__rio___auto__1 = _init_l_Std_TreeSet_toList__rio___auto__1();
    lean_mark_persistent(l_Std_TreeSet_toList__rio___auto__1);
    l_Std_TreeSet_instSliceableRciSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRciSlice___auto__1();
    lean_mark_persistent(l_Std_TreeSet_instSliceableRciSlice___auto__1);
    l_Std_TreeSet_toList__rci___auto__1 = _init_l_Std_TreeSet_toList__rci___auto__1();
    lean_mark_persistent(l_Std_TreeSet_toList__rci___auto__1);
    l_Std_TreeSet_instSliceableRcoSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRcoSlice___auto__1();
    lean_mark_persistent(l_Std_TreeSet_instSliceableRcoSlice___auto__1);
    l_Std_TreeSet_toList__rco___auto__1 = _init_l_Std_TreeSet_toList__rco___auto__1();
    lean_mark_persistent(l_Std_TreeSet_toList__rco___auto__1);
    l_Std_TreeSet_instSliceableRccSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRccSlice___auto__1();
    lean_mark_persistent(l_Std_TreeSet_instSliceableRccSlice___auto__1);
    l_Std_TreeSet_toList__rcc___auto__1 = _init_l_Std_TreeSet_toList__rcc___auto__1();
    lean_mark_persistent(l_Std_TreeSet_toList__rcc___auto__1);
    l_Std_TreeSet_instSliceableRoiSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRoiSlice___auto__1();
    lean_mark_persistent(l_Std_TreeSet_instSliceableRoiSlice___auto__1);
    l_Std_TreeSet_toList__roi___auto__1 = _init_l_Std_TreeSet_toList__roi___auto__1();
    lean_mark_persistent(l_Std_TreeSet_toList__roi___auto__1);
    l_Std_TreeSet_instSliceableRocSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRocSlice___auto__1();
    lean_mark_persistent(l_Std_TreeSet_instSliceableRocSlice___auto__1);
    l_Std_TreeSet_toList__roc___auto__1 = _init_l_Std_TreeSet_toList__roc___auto__1();
    lean_mark_persistent(l_Std_TreeSet_toList__roc___auto__1);
    l_Std_TreeSet_instSliceableRooSlice___auto__1 =
        _init_l_Std_TreeSet_instSliceableRooSlice___auto__1();
    lean_mark_persistent(l_Std_TreeSet_instSliceableRooSlice___auto__1);
    l_Std_TreeSet_toList__roo___auto__1 = _init_l_Std_TreeSet_toList__roo___auto__1();
    lean_mark_persistent(l_Std_TreeSet_toList__roo___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeSet_Slice(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeSet_Raw_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Slice(builtin);
}

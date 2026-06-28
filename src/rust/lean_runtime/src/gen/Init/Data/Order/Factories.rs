// Lean compiler output
// Module: Init.Data.Order.Factories
// Imports: Init.Data.Order.Classes Init.Classical
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_mkAtom,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2, lean_box,
    lean_closure_set, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_IsPreorder_of__le___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_Std_IsPreorder_of__le___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Std_IsPreorder_of__le___auto__1___closed__1_value: LeanStringObject<7> =
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
static mut l_Std_IsPreorder_of__le___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Std_IsPreorder_of__le___auto__1___closed__2_value: LeanStringObject<7> =
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
static mut l_Std_IsPreorder_of__le___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Std_IsPreorder_of__le___auto__1___closed__3_value: LeanStringObject<10> =
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
static mut l_Std_IsPreorder_of__le___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__3_value) as *mut LeanObject;
static l_Std_IsPreorder_of__le___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_IsPreorder_of__le___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_IsPreorder_of__le___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_IsPreorder_of__le___auto__1___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Std_IsPreorder_of__le___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Std_IsPreorder_of__le___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Std_IsPreorder_of__le___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Std_IsPreorder_of__le___auto__1___closed__6_value: LeanStringObject<19> =
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
static mut l_Std_IsPreorder_of__le___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__6_value) as *mut LeanObject;
static l_Std_IsPreorder_of__le___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_IsPreorder_of__le___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_IsPreorder_of__le___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_IsPreorder_of__le___auto__1___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Std_IsPreorder_of__le___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Std_IsPreorder_of__le___auto__1___closed__8_value: LeanStringObject<5> =
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
static mut l_Std_IsPreorder_of__le___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Std_IsPreorder_of__le___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Std_IsPreorder_of__le___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Std_IsPreorder_of__le___auto__1___closed__10_value: LeanStringObject<6> =
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
static mut l_Std_IsPreorder_of__le___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__10_value) as *mut LeanObject;
static l_Std_IsPreorder_of__le___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_IsPreorder_of__le___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_IsPreorder_of__le___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_IsPreorder_of__le___auto__1___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Std_IsPreorder_of__le___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Std_IsPreorder_of__le___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_IsPreorder_of__le___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_IsPreorder_of__le___auto__1___closed__14_value: LeanStringObject<14> =
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
            105, 110, 102, 101, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0,
        ],
    };
static mut l_Std_IsPreorder_of__le___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__14_value) as *mut LeanObject;
static mut l_Std_IsPreorder_of__le___auto__1___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_IsPreorder_of__le___auto__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_IsPreorder_of__le___auto__1___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__14_value)
                as *mut LeanObject,
            5508559176583389713 as *mut LeanObject,
        ],
    };
static mut l_Std_IsPreorder_of__le___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IsPreorder_of__le___auto__1___closed__17_value) as *mut LeanObject;
static mut l_Std_IsPreorder_of__le___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_IsPreorder_of__le___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_IsPreorder_of__le___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_IsPreorder_of__le___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_IsPreorder_of__le___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_IsPreorder_of__le___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_IsPreorder_of__le___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_IsPreorder_of__le___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_IsPreorder_of__le___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_IsPreorder_of__le___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsPreorder_of__le___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsPreorder_of__le___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsLinearPreorder_of__le___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsLinearPreorder_of__le___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsPartialOrder_of__le___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsPartialOrder_of__le___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsPartialOrder_of__le___auto__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsLinearOrder_of__le___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsLinearOrder_of__le___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsLinearOrder_of__le___auto__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__0_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 97, 119, 102, 117, 108, 79, 114, 100, 101, 114, 73, 110, 102, 46, 108, 101, 95,
            109, 105, 110, 95, 105, 102, 102, 0,
        ],
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__0_value)
        as *mut LeanObject;
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__3_value: LeanStringObject<15> =
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
            76, 97, 119, 102, 117, 108, 79, 114, 100, 101, 114, 73, 110, 102, 0,
        ],
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__3_value)
        as *mut LeanObject;
pub static l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__4_value: LeanStringObject<11> =
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
        m_data: [108, 101, 95, 109, 105, 110, 95, 105, 102, 102, 0],
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__4_value)
        as *mut LeanObject;
static l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__3_value)
                as *mut LeanObject,
            1447659726466104677 as *mut LeanObject,
        ],
    };
pub static l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__5_value: LeanCtorObject<3> =
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
                l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__4_value)
                as *mut LeanObject,
            11688598461284269209 as *mut LeanObject,
        ],
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__5_value)
        as *mut LeanObject;
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            77, 105, 110, 69, 113, 79, 114, 46, 109, 105, 110, 95, 101, 113, 95, 111, 114, 0,
        ],
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__0_value)
        as *mut LeanObject;
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__3_value: LeanStringObject<8> =
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
        m_data: [77, 105, 110, 69, 113, 79, 114, 0],
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__3_value)
        as *mut LeanObject;
pub static l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__4_value: LeanStringObject<10> =
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
        m_data: [109, 105, 110, 95, 101, 113, 95, 111, 114, 0],
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__4_value)
        as *mut LeanObject;
static l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__3_value)
                as *mut LeanObject,
            4823930919564622049 as *mut LeanObject,
        ],
    };
pub static l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__5_value: LeanCtorObject<3> =
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
                l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__4_value)
                as *mut LeanObject,
            8935362175873358633 as *mut LeanObject,
        ],
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__5_value)
        as *mut LeanObject;
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_LawfulOrderMin_of__le__min__iff___auto__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_LawfulOrderMin_of__min__le___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            77, 97, 120, 69, 113, 79, 114, 46, 109, 97, 120, 95, 101, 113, 95, 111, 114, 0,
        ],
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__0_value)
        as *mut LeanObject;
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__3_value: LeanStringObject<8> =
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
        m_data: [77, 97, 120, 69, 113, 79, 114, 0],
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__3_value)
        as *mut LeanObject;
pub static l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__4_value: LeanStringObject<10> =
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
        m_data: [109, 97, 120, 95, 101, 113, 95, 111, 114, 0],
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__4_value)
        as *mut LeanObject;
static l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__3_value)
                as *mut LeanObject,
            11589081371622347205 as *mut LeanObject,
        ],
    };
pub static l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__5_value: LeanCtorObject<3> =
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
                l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__4_value)
                as *mut LeanObject,
            7825539582434025008 as *mut LeanObject,
        ],
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__5_value)
        as *mut LeanObject;
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_LawfulOrderMax_of__max__le__iff___auto__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_LawfulOrderMax_of__le__max___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsLinearPreorder_of__lt___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsLinearPreorder_of__lt___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsLinearOrder_of__lt___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsLinearOrder_of__lt___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_IsLinearOrder_of__lt___auto__5: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Min_leftLeaningOfLE___redArg___lam__0(
    mut v_inst_255_: *mut LeanObject,
    mut v_a_256_: *mut LeanObject,
    mut v_b_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_259_: u8 = 0;
    lean_inc(v_b_257_);
    lean_inc(v_a_256_);
    v___x_258_ = lean_apply_2(v_inst_255_, v_a_256_, v_b_257_);
    v___x_259_ = (lean_unbox(v___x_258_) as u8);
    if v___x_259_ == 0 {
        lean_dec(v_a_256_);
        return v_b_257_;
    } else {
        lean_dec(v_b_257_);
        return v_a_256_;
    }
}
pub unsafe fn l_Min_leftLeaningOfLE___redArg(mut v_inst_260_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_261_: *mut LeanObject = core::ptr::null_mut();
    v___f_261_ = lean_alloc_closure(
        l_Min_leftLeaningOfLE___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_261_, 0, v_inst_260_);
    return v___f_261_;
}
pub unsafe fn l_Min_leftLeaningOfLE(
    mut v_00_u03b1_262_: *mut LeanObject,
    mut v_inst_263_: *mut LeanObject,
    mut v_inst_264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_265_: *mut LeanObject = core::ptr::null_mut();
    v___f_265_ = lean_alloc_closure(
        l_Min_leftLeaningOfLE___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_265_, 0, v_inst_264_);
    return v___f_265_;
}
pub unsafe fn l_Max_leftLeaningOfLE___redArg___lam__0(
    mut v_inst_266_: *mut LeanObject,
    mut v_a_267_: *mut LeanObject,
    mut v_b_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: u8 = 0;
    lean_inc(v_a_267_);
    lean_inc(v_b_268_);
    v___x_269_ = lean_apply_2(v_inst_266_, v_b_268_, v_a_267_);
    v___x_270_ = (lean_unbox(v___x_269_) as u8);
    if v___x_270_ == 0 {
        lean_dec(v_a_267_);
        return v_b_268_;
    } else {
        lean_dec(v_b_268_);
        return v_a_267_;
    }
}
pub unsafe fn l_Max_leftLeaningOfLE___redArg(mut v_inst_271_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_272_: *mut LeanObject = core::ptr::null_mut();
    v___f_272_ = lean_alloc_closure(
        l_Max_leftLeaningOfLE___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_272_, 0, v_inst_271_);
    return v___f_272_;
}
pub unsafe fn l_Max_leftLeaningOfLE(
    mut v_00_u03b1_273_: *mut LeanObject,
    mut v_inst_274_: *mut LeanObject,
    mut v_inst_275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_276_: *mut LeanObject = core::ptr::null_mut();
    v___f_276_ = lean_alloc_closure(
        l_Max_leftLeaningOfLE___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_276_, 0, v_inst_275_);
    return v___f_276_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    v___x_303_ = l_Std_IsPreorder_of__le___auto__1___closed__10;
    v___x_304_ = l_Lean_mkAtom(v___x_303_);
    return v___x_304_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    v___x_305_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__12_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__12,
    );
    v___x_306_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_307_ = lean_array_push(v___x_306_, v___x_305_);
    return v___x_307_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__15() -> *mut LeanObject {
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    v___x_309_ = l_Std_IsPreorder_of__le___auto__1___closed__14;
    v___x_310_ = lean_string_utf8_byte_size(v___x_309_);
    return v___x_310_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__16() -> *mut LeanObject {
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    v___x_311_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__15_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__15,
    );
    v___x_312_ = lean_unsigned_to_nat(0);
    v___x_313_ = l_Std_IsPreorder_of__le___auto__1___closed__14;
    v___x_314_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_314_, 0, v___x_313_);
    lean_ctor_set(v___x_314_, 1, v___x_312_);
    lean_ctor_set(v___x_314_, 2, v___x_311_);
    return v___x_314_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    v___x_317_ = lean_box(0);
    v___x_318_ = l_Std_IsPreorder_of__le___auto__1___closed__17;
    v___x_319_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__16_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__16,
    );
    v___x_320_ = lean_box(2);
    v___x_321_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_321_, 0, v___x_320_);
    lean_ctor_set(v___x_321_, 1, v___x_319_);
    lean_ctor_set(v___x_321_, 2, v___x_318_);
    lean_ctor_set(v___x_321_, 3, v___x_317_);
    return v___x_321_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    v___x_322_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__18_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__18,
    );
    v___x_323_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__13_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__13,
    );
    v___x_324_ = lean_array_push(v___x_323_, v___x_322_);
    return v___x_324_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    v___x_325_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__19_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__19,
    );
    v___x_326_ = l_Std_IsPreorder_of__le___auto__1___closed__11;
    v___x_327_ = lean_box(2);
    v___x_328_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_328_, 0, v___x_327_);
    lean_ctor_set(v___x_328_, 1, v___x_326_);
    lean_ctor_set(v___x_328_, 2, v___x_325_);
    return v___x_328_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    v___x_329_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__20_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__20,
    );
    v___x_330_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_331_ = lean_array_push(v___x_330_, v___x_329_);
    return v___x_331_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    v___x_332_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__21_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__21,
    );
    v___x_333_ = l_Std_IsPreorder_of__le___auto__1___closed__9;
    v___x_334_ = lean_box(2);
    v___x_335_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_335_, 0, v___x_334_);
    lean_ctor_set(v___x_335_, 1, v___x_333_);
    lean_ctor_set(v___x_335_, 2, v___x_332_);
    return v___x_335_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    v___x_336_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__22_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__22,
    );
    v___x_337_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_338_ = lean_array_push(v___x_337_, v___x_336_);
    return v___x_338_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_339_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__23_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__23,
    );
    v___x_340_ = l_Std_IsPreorder_of__le___auto__1___closed__7;
    v___x_341_ = lean_box(2);
    v___x_342_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_342_, 0, v___x_341_);
    lean_ctor_set(v___x_342_, 1, v___x_340_);
    lean_ctor_set(v___x_342_, 2, v___x_339_);
    return v___x_342_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    v___x_343_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__24_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__24,
    );
    v___x_344_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_345_ = lean_array_push(v___x_344_, v___x_343_);
    return v___x_345_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v___x_346_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__25_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__25,
    );
    v___x_347_ = l_Std_IsPreorder_of__le___auto__1___closed__4;
    v___x_348_ = lean_box(2);
    v___x_349_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_349_, 0, v___x_348_);
    lean_ctor_set(v___x_349_, 1, v___x_347_);
    lean_ctor_set(v___x_349_, 2, v___x_346_);
    return v___x_349_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__1() -> *mut LeanObject {
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    v___x_350_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_350_;
}
pub unsafe fn _init_l_Std_IsPreorder_of__le___auto__3() -> *mut LeanObject {
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    v___x_351_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_351_;
}
pub unsafe fn _init_l_Std_IsLinearPreorder_of__le___auto__1() -> *mut LeanObject {
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    v___x_352_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_352_;
}
pub unsafe fn _init_l_Std_IsLinearPreorder_of__le___auto__3() -> *mut LeanObject {
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    v___x_353_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_353_;
}
pub unsafe fn _init_l_Std_IsPartialOrder_of__le___auto__1() -> *mut LeanObject {
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    v___x_354_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_354_;
}
pub unsafe fn _init_l_Std_IsPartialOrder_of__le___auto__3() -> *mut LeanObject {
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    v___x_355_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_355_;
}
pub unsafe fn _init_l_Std_IsPartialOrder_of__le___auto__5() -> *mut LeanObject {
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    v___x_356_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_356_;
}
pub unsafe fn _init_l_Std_IsLinearOrder_of__le___auto__1() -> *mut LeanObject {
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    v___x_357_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_357_;
}
pub unsafe fn _init_l_Std_IsLinearOrder_of__le___auto__3() -> *mut LeanObject {
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    v___x_358_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_358_;
}
pub unsafe fn _init_l_Std_IsLinearOrder_of__le___auto__5() -> *mut LeanObject {
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    v___x_359_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_359_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__1() -> *mut LeanObject
{
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    v___x_361_ = l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__0;
    v___x_362_ = lean_string_utf8_byte_size(v___x_361_);
    return v___x_362_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__2() -> *mut LeanObject
{
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    v___x_363_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__1_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__1,
    );
    v___x_364_ = lean_unsigned_to_nat(0);
    v___x_365_ = l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__0;
    v___x_366_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_366_, 0, v___x_365_);
    lean_ctor_set(v___x_366_, 1, v___x_364_);
    lean_ctor_set(v___x_366_, 2, v___x_363_);
    return v___x_366_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__6() -> *mut LeanObject
{
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    v___x_372_ = lean_box(0);
    v___x_373_ = l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__5;
    v___x_374_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__2_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__2,
    );
    v___x_375_ = lean_box(2);
    v___x_376_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_376_, 0, v___x_375_);
    lean_ctor_set(v___x_376_, 1, v___x_374_);
    lean_ctor_set(v___x_376_, 2, v___x_373_);
    lean_ctor_set(v___x_376_, 3, v___x_372_);
    return v___x_376_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__7() -> *mut LeanObject
{
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    v___x_377_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__6),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__6_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__6,
    );
    v___x_378_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__13_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__13,
    );
    v___x_379_ = lean_array_push(v___x_378_, v___x_377_);
    return v___x_379_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__8() -> *mut LeanObject
{
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    v___x_380_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__7),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__7_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__7,
    );
    v___x_381_ = l_Std_IsPreorder_of__le___auto__1___closed__11;
    v___x_382_ = lean_box(2);
    v___x_383_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_383_, 0, v___x_382_);
    lean_ctor_set(v___x_383_, 1, v___x_381_);
    lean_ctor_set(v___x_383_, 2, v___x_380_);
    return v___x_383_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__9() -> *mut LeanObject
{
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    v___x_384_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__8),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__8_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__8,
    );
    v___x_385_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_386_ = lean_array_push(v___x_385_, v___x_384_);
    return v___x_386_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__10() -> *mut LeanObject
{
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    v___x_387_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__9),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__9_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__9,
    );
    v___x_388_ = l_Std_IsPreorder_of__le___auto__1___closed__9;
    v___x_389_ = lean_box(2);
    v___x_390_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_390_, 0, v___x_389_);
    lean_ctor_set(v___x_390_, 1, v___x_388_);
    lean_ctor_set(v___x_390_, 2, v___x_387_);
    return v___x_390_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__11() -> *mut LeanObject
{
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    v___x_391_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__10),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__10_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__10,
    );
    v___x_392_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_393_ = lean_array_push(v___x_392_, v___x_391_);
    return v___x_393_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__12() -> *mut LeanObject
{
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    v___x_394_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__11),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__11_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__11,
    );
    v___x_395_ = l_Std_IsPreorder_of__le___auto__1___closed__7;
    v___x_396_ = lean_box(2);
    v___x_397_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_397_, 0, v___x_396_);
    lean_ctor_set(v___x_397_, 1, v___x_395_);
    lean_ctor_set(v___x_397_, 2, v___x_394_);
    return v___x_397_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__13() -> *mut LeanObject
{
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__12_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__12,
    );
    v___x_399_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_400_ = lean_array_push(v___x_399_, v___x_398_);
    return v___x_400_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__14() -> *mut LeanObject
{
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    v___x_401_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__13_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__13,
    );
    v___x_402_ = l_Std_IsPreorder_of__le___auto__1___closed__4;
    v___x_403_ = lean_box(2);
    v___x_404_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_404_, 0, v___x_403_);
    lean_ctor_set(v___x_404_, 1, v___x_402_);
    lean_ctor_set(v___x_404_, 2, v___x_401_);
    return v___x_404_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1() -> *mut LeanObject {
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    v___x_405_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__14_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__14,
    );
    return v___x_405_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__1() -> *mut LeanObject
{
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    v___x_407_ = l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__0;
    v___x_408_ = lean_string_utf8_byte_size(v___x_407_);
    return v___x_408_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__2() -> *mut LeanObject
{
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    v___x_409_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__1),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__1_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__1,
    );
    v___x_410_ = lean_unsigned_to_nat(0);
    v___x_411_ = l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__0;
    v___x_412_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_412_, 0, v___x_411_);
    lean_ctor_set(v___x_412_, 1, v___x_410_);
    lean_ctor_set(v___x_412_, 2, v___x_409_);
    return v___x_412_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__6() -> *mut LeanObject
{
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_418_ = lean_box(0);
    v___x_419_ = l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__5;
    v___x_420_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__2),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__2_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__2,
    );
    v___x_421_ = lean_box(2);
    v___x_422_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_422_, 0, v___x_421_);
    lean_ctor_set(v___x_422_, 1, v___x_420_);
    lean_ctor_set(v___x_422_, 2, v___x_419_);
    lean_ctor_set(v___x_422_, 3, v___x_418_);
    return v___x_422_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__7() -> *mut LeanObject
{
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    v___x_423_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__6),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__6_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__6,
    );
    v___x_424_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__13_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__13,
    );
    v___x_425_ = lean_array_push(v___x_424_, v___x_423_);
    return v___x_425_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__8() -> *mut LeanObject
{
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    v___x_426_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__7),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__7_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__7,
    );
    v___x_427_ = l_Std_IsPreorder_of__le___auto__1___closed__11;
    v___x_428_ = lean_box(2);
    v___x_429_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_429_, 0, v___x_428_);
    lean_ctor_set(v___x_429_, 1, v___x_427_);
    lean_ctor_set(v___x_429_, 2, v___x_426_);
    return v___x_429_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__9() -> *mut LeanObject
{
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    v___x_430_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__8),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__8_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__8,
    );
    v___x_431_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_432_ = lean_array_push(v___x_431_, v___x_430_);
    return v___x_432_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__10() -> *mut LeanObject
{
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    v___x_433_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__9),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__9_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__9,
    );
    v___x_434_ = l_Std_IsPreorder_of__le___auto__1___closed__9;
    v___x_435_ = lean_box(2);
    v___x_436_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_436_, 0, v___x_435_);
    lean_ctor_set(v___x_436_, 1, v___x_434_);
    lean_ctor_set(v___x_436_, 2, v___x_433_);
    return v___x_436_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__11() -> *mut LeanObject
{
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    v___x_437_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__10),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__10_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__10,
    );
    v___x_438_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_439_ = lean_array_push(v___x_438_, v___x_437_);
    return v___x_439_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__12() -> *mut LeanObject
{
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    v___x_440_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__11),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__11_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__11,
    );
    v___x_441_ = l_Std_IsPreorder_of__le___auto__1___closed__7;
    v___x_442_ = lean_box(2);
    v___x_443_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_443_, 0, v___x_442_);
    lean_ctor_set(v___x_443_, 1, v___x_441_);
    lean_ctor_set(v___x_443_, 2, v___x_440_);
    return v___x_443_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__13() -> *mut LeanObject
{
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    v___x_444_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__12),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__12_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__12,
    );
    v___x_445_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_446_ = lean_array_push(v___x_445_, v___x_444_);
    return v___x_446_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__14() -> *mut LeanObject
{
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    v___x_447_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__13),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__13_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__13,
    );
    v___x_448_ = l_Std_IsPreorder_of__le___auto__1___closed__4;
    v___x_449_ = lean_box(2);
    v___x_450_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_450_, 0, v___x_449_);
    lean_ctor_set(v___x_450_, 1, v___x_448_);
    lean_ctor_set(v___x_450_, 2, v___x_447_);
    return v___x_450_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3() -> *mut LeanObject {
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    v___x_451_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__14),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__14_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__14,
    );
    return v___x_451_;
}
pub unsafe fn _init_l_Std_LawfulOrderMin_of__min__le___auto__1() -> *mut LeanObject {
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    v___x_452_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__14),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__14_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3___closed__14,
    );
    return v___x_452_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__1() -> *mut LeanObject {
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    v___x_453_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__14_once),
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1___closed__14,
    );
    return v___x_453_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__1() -> *mut LeanObject
{
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    v___x_455_ = l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__0;
    v___x_456_ = lean_string_utf8_byte_size(v___x_455_);
    return v___x_456_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__2() -> *mut LeanObject
{
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    v___x_457_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__1),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__1_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__1,
    );
    v___x_458_ = lean_unsigned_to_nat(0);
    v___x_459_ = l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__0;
    v___x_460_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_460_, 0, v___x_459_);
    lean_ctor_set(v___x_460_, 1, v___x_458_);
    lean_ctor_set(v___x_460_, 2, v___x_457_);
    return v___x_460_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__6() -> *mut LeanObject
{
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    v___x_466_ = lean_box(0);
    v___x_467_ = l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__5;
    v___x_468_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__2),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__2_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__2,
    );
    v___x_469_ = lean_box(2);
    v___x_470_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_470_, 0, v___x_469_);
    lean_ctor_set(v___x_470_, 1, v___x_468_);
    lean_ctor_set(v___x_470_, 2, v___x_467_);
    lean_ctor_set(v___x_470_, 3, v___x_466_);
    return v___x_470_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__7() -> *mut LeanObject
{
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    v___x_471_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__6),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__6_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__6,
    );
    v___x_472_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__13_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__13,
    );
    v___x_473_ = lean_array_push(v___x_472_, v___x_471_);
    return v___x_473_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__8() -> *mut LeanObject
{
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    v___x_474_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__7),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__7_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__7,
    );
    v___x_475_ = l_Std_IsPreorder_of__le___auto__1___closed__11;
    v___x_476_ = lean_box(2);
    v___x_477_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_477_, 0, v___x_476_);
    lean_ctor_set(v___x_477_, 1, v___x_475_);
    lean_ctor_set(v___x_477_, 2, v___x_474_);
    return v___x_477_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__9() -> *mut LeanObject
{
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    v___x_478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__8),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__8_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__8,
    );
    v___x_479_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_480_ = lean_array_push(v___x_479_, v___x_478_);
    return v___x_480_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__10() -> *mut LeanObject
{
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    v___x_481_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__9),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__9_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__9,
    );
    v___x_482_ = l_Std_IsPreorder_of__le___auto__1___closed__9;
    v___x_483_ = lean_box(2);
    v___x_484_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_484_, 0, v___x_483_);
    lean_ctor_set(v___x_484_, 1, v___x_482_);
    lean_ctor_set(v___x_484_, 2, v___x_481_);
    return v___x_484_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__11() -> *mut LeanObject
{
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    v___x_485_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__10),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__10_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__10,
    );
    v___x_486_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_487_ = lean_array_push(v___x_486_, v___x_485_);
    return v___x_487_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__12() -> *mut LeanObject
{
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    v___x_488_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__11),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__11_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__11,
    );
    v___x_489_ = l_Std_IsPreorder_of__le___auto__1___closed__7;
    v___x_490_ = lean_box(2);
    v___x_491_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_491_, 0, v___x_490_);
    lean_ctor_set(v___x_491_, 1, v___x_489_);
    lean_ctor_set(v___x_491_, 2, v___x_488_);
    return v___x_491_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__13() -> *mut LeanObject
{
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    v___x_492_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__12),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__12_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__12,
    );
    v___x_493_ = l_Std_IsPreorder_of__le___auto__1___closed__5;
    v___x_494_ = lean_array_push(v___x_493_, v___x_492_);
    return v___x_494_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__14() -> *mut LeanObject
{
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    v___x_495_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__13),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__13_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__13,
    );
    v___x_496_ = l_Std_IsPreorder_of__le___auto__1___closed__4;
    v___x_497_ = lean_box(2);
    v___x_498_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_498_, 0, v___x_497_);
    lean_ctor_set(v___x_498_, 1, v___x_496_);
    lean_ctor_set(v___x_498_, 2, v___x_495_);
    return v___x_498_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3() -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__14),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__14_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__14,
    );
    return v___x_499_;
}
pub unsafe fn _init_l_Std_LawfulOrderMax_of__le__max___auto__1() -> *mut LeanObject {
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    v___x_500_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__14),
        core::ptr::addr_of_mut!(l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__14_once),
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3___closed__14,
    );
    return v___x_500_;
}
pub unsafe fn l_LE_ofLT(
    mut v_00_u03b1_501_: *mut LeanObject,
    mut v_inst_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    v___x_503_ = lean_box(0);
    return v___x_503_;
}
pub unsafe fn _init_l_Std_IsLinearPreorder_of__lt___auto__1() -> *mut LeanObject {
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    v___x_504_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_504_;
}
pub unsafe fn _init_l_Std_IsLinearPreorder_of__lt___auto__3() -> *mut LeanObject {
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    v___x_505_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_505_;
}
pub unsafe fn _init_l_Std_IsLinearOrder_of__lt___auto__1() -> *mut LeanObject {
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    v___x_506_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_506_;
}
pub unsafe fn _init_l_Std_IsLinearOrder_of__lt___auto__3() -> *mut LeanObject {
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    v___x_507_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_507_;
}
pub unsafe fn _init_l_Std_IsLinearOrder_of__lt___auto__5() -> *mut LeanObject {
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    v___x_508_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IsPreorder_of__le___auto__1___closed__26_once),
        _init_l_Std_IsPreorder_of__le___auto__1___closed__26,
    );
    return v___x_508_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Order_Factories(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Order_Factories(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_IsPreorder_of__le___auto__1 = _init_l_Std_IsPreorder_of__le___auto__1();
    lean_mark_persistent(l_Std_IsPreorder_of__le___auto__1);
    l_Std_IsPreorder_of__le___auto__3 = _init_l_Std_IsPreorder_of__le___auto__3();
    lean_mark_persistent(l_Std_IsPreorder_of__le___auto__3);
    l_Std_IsLinearPreorder_of__le___auto__1 = _init_l_Std_IsLinearPreorder_of__le___auto__1();
    lean_mark_persistent(l_Std_IsLinearPreorder_of__le___auto__1);
    l_Std_IsLinearPreorder_of__le___auto__3 = _init_l_Std_IsLinearPreorder_of__le___auto__3();
    lean_mark_persistent(l_Std_IsLinearPreorder_of__le___auto__3);
    l_Std_IsPartialOrder_of__le___auto__1 = _init_l_Std_IsPartialOrder_of__le___auto__1();
    lean_mark_persistent(l_Std_IsPartialOrder_of__le___auto__1);
    l_Std_IsPartialOrder_of__le___auto__3 = _init_l_Std_IsPartialOrder_of__le___auto__3();
    lean_mark_persistent(l_Std_IsPartialOrder_of__le___auto__3);
    l_Std_IsPartialOrder_of__le___auto__5 = _init_l_Std_IsPartialOrder_of__le___auto__5();
    lean_mark_persistent(l_Std_IsPartialOrder_of__le___auto__5);
    l_Std_IsLinearOrder_of__le___auto__1 = _init_l_Std_IsLinearOrder_of__le___auto__1();
    lean_mark_persistent(l_Std_IsLinearOrder_of__le___auto__1);
    l_Std_IsLinearOrder_of__le___auto__3 = _init_l_Std_IsLinearOrder_of__le___auto__3();
    lean_mark_persistent(l_Std_IsLinearOrder_of__le___auto__3);
    l_Std_IsLinearOrder_of__le___auto__5 = _init_l_Std_IsLinearOrder_of__le___auto__5();
    lean_mark_persistent(l_Std_IsLinearOrder_of__le___auto__5);
    l_Std_LawfulOrderMin_of__le__min__iff___auto__1 =
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__1();
    lean_mark_persistent(l_Std_LawfulOrderMin_of__le__min__iff___auto__1);
    l_Std_LawfulOrderMin_of__le__min__iff___auto__3 =
        _init_l_Std_LawfulOrderMin_of__le__min__iff___auto__3();
    lean_mark_persistent(l_Std_LawfulOrderMin_of__le__min__iff___auto__3);
    l_Std_LawfulOrderMin_of__min__le___auto__1 = _init_l_Std_LawfulOrderMin_of__min__le___auto__1();
    lean_mark_persistent(l_Std_LawfulOrderMin_of__min__le___auto__1);
    l_Std_LawfulOrderMax_of__max__le__iff___auto__1 =
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__1();
    lean_mark_persistent(l_Std_LawfulOrderMax_of__max__le__iff___auto__1);
    l_Std_LawfulOrderMax_of__max__le__iff___auto__3 =
        _init_l_Std_LawfulOrderMax_of__max__le__iff___auto__3();
    lean_mark_persistent(l_Std_LawfulOrderMax_of__max__le__iff___auto__3);
    l_Std_LawfulOrderMax_of__le__max___auto__1 = _init_l_Std_LawfulOrderMax_of__le__max___auto__1();
    lean_mark_persistent(l_Std_LawfulOrderMax_of__le__max___auto__1);
    l_Std_IsLinearPreorder_of__lt___auto__1 = _init_l_Std_IsLinearPreorder_of__lt___auto__1();
    lean_mark_persistent(l_Std_IsLinearPreorder_of__lt___auto__1);
    l_Std_IsLinearPreorder_of__lt___auto__3 = _init_l_Std_IsLinearPreorder_of__lt___auto__3();
    lean_mark_persistent(l_Std_IsLinearPreorder_of__lt___auto__3);
    l_Std_IsLinearOrder_of__lt___auto__1 = _init_l_Std_IsLinearOrder_of__lt___auto__1();
    lean_mark_persistent(l_Std_IsLinearOrder_of__lt___auto__1);
    l_Std_IsLinearOrder_of__lt___auto__3 = _init_l_Std_IsLinearOrder_of__lt___auto__3();
    lean_mark_persistent(l_Std_IsLinearOrder_of__lt___auto__3);
    l_Std_IsLinearOrder_of__lt___auto__5 = _init_l_Std_IsLinearOrder_of__lt___auto__5();
    lean_mark_persistent(l_Std_IsLinearOrder_of__lt___auto__5);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Order_Factories(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Factories(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Order_Factories(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Order_Factories(builtin);
}

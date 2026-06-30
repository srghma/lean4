// Lean compiler output
// Module: Std.Data.Iterators.Consumers.Set
// Imports: Std.Data.Iterators.Consumers.Monadic.Set Init.Data.Iterators.Consumers.Total
use crate::ffi::{lean_array_push, lean_mk_array, lean_string_utf8_byte_size};
use crate::r#gen::Init::Data::Iterators::Consumers::Total::{
    initialize_Init_Data_Iterators_Consumers_Total,
    runtime_initialize_Init_Data_Iterators_Consumers_Total,
};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_contains___redArg;
use crate::r#gen::Std::Data::Iterators::Consumers::Monadic::Set::{
    initialize_Std_Data_Iterators_Consumers_Monadic_Set,
    runtime_initialize_Std_Data_Iterators_Consumers_Monadic_Set,
};
pub static l_Std_Iter_toHashSet___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Iter_toHashSet___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Iter_toHashSet___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toHashSet___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Iter_toHashSet___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toHashSet___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toHashSet___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toHashSet___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Iter_toTreeSet___auto__1___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Iter_toTreeSet___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Iter_toTreeSet___auto__1___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Iter_toTreeSet___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Iter_toTreeSet___auto__1___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Iter_toTreeSet___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Iter_toTreeSet___auto__1___closed__3_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Iter_toTreeSet___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Iter_toTreeSet___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Iter_toTreeSet___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Iter_toTreeSet___auto__1___closed__6_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Iter_toTreeSet___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Iter_toTreeSet___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Iter_toTreeSet___auto__1___closed__8_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Iter_toTreeSet___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Iter_toTreeSet___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Iter_toTreeSet___auto__1___closed__10_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Iter_toTreeSet___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Iter_toTreeSet___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_Iter_toTreeSet___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toTreeSet___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Iter_toTreeSet___auto__1___closed__14_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Iter_toTreeSet___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Std_Iter_toTreeSet___auto__1___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toTreeSet___auto__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Iter_toTreeSet___auto__1___closed__17_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16710690322389477741 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toTreeSet___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Std_Iter_toTreeSet___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toTreeSet___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toTreeSet___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toTreeSet___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toTreeSet___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toTreeSet___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toTreeSet___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toTreeSet___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Iter_toTreeSet___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Iter_toTreeSet___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Iter_toTreeSet___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Iter_Total_toTreeSet___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Iter_toExtTreeSet___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Iter_Total_toExtTreeSet___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Iter_toHashSet___redArg___lam__0(
    mut v_x_348_: *mut leanh::LeanObject,
    mut v_x_349_: *mut leanh::LeanObject,
    mut v_f_350_: *mut leanh::LeanObject,
    mut v_x_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_352_ = leanh::lean_apply_1(v_f_350_, v_x_351_);
    return v___x_352_;
}
pub unsafe fn l_Std_Iter_toHashSet___redArg___lam__1(
    mut v_inst_353_: *mut leanh::LeanObject,
    mut v_inst_354_: *mut leanh::LeanObject,
    mut v_x1_355_: *mut leanh::LeanObject,
    mut v_x2_356_: *mut leanh::LeanObject,
    mut v_x3_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = leanh::lean_box(0);
    v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_353_,
        v_inst_354_,
        v_x3_357_,
        v_x1_355_,
        v___x_358_,
    );
    v___x_360_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_360_, 0, v___x_359_);
    return v___x_360_;
}
pub unsafe fn _init_l_Std_Iter_toHashSet___redArg___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = leanh::lean_box(0);
    v___x_363_ = leanh::lean_unsigned_to_nat(16);
    v___x_364_ = lean_mk_array(v___x_363_, v___x_362_);
    return v___x_364_;
}
pub unsafe fn _init_l_Std_Iter_toHashSet___redArg___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_365_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__1_once),
        _init_l_Std_Iter_toHashSet___redArg___closed__1,
    );
    v___x_366_ = leanh::lean_unsigned_to_nat(0);
    v___x_367_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_367_, 0, v___x_366_);
    leanh::lean_ctor_set(v___x_367_, 1, v___x_365_);
    return v___x_367_;
}
pub unsafe fn l_Std_Iter_toHashSet___redArg(
    mut v_inst_368_: *mut leanh::LeanObject,
    mut v_inst_369_: *mut leanh::LeanObject,
    mut v_inst_370_: *mut leanh::LeanObject,
    mut v_it_371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_372_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_373_ = leanh::lean_alloc_closure(
        l_Std_Iter_toHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_373_, 0, v_inst_368_);
    leanh::lean_closure_set(v___f_373_, 1, v_inst_369_);
    v___x_374_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2_once),
        _init_l_Std_Iter_toHashSet___redArg___closed__2,
    );
    v___x_375_ = leanh::lean_apply_6(
        v_inst_370_,
        v___f_372_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_371_,
        v___x_374_,
        v___f_373_,
    );
    return v___x_375_;
}
pub unsafe fn l_Std_Iter_toHashSet(
    mut v_00_u03b1_376_: *mut leanh::LeanObject,
    mut v_00_u03b2_377_: *mut leanh::LeanObject,
    mut v_inst_378_: *mut leanh::LeanObject,
    mut v_inst_379_: *mut leanh::LeanObject,
    mut v_inst_380_: *mut leanh::LeanObject,
    mut v_inst_381_: *mut leanh::LeanObject,
    mut v_it_382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_383_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_384_ = leanh::lean_alloc_closure(
        l_Std_Iter_toHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_384_, 0, v_inst_378_);
    leanh::lean_closure_set(v___f_384_, 1, v_inst_379_);
    v___x_385_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2_once),
        _init_l_Std_Iter_toHashSet___redArg___closed__2,
    );
    v___x_386_ = leanh::lean_apply_6(
        v_inst_381_,
        v___f_383_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_382_,
        v___x_385_,
        v___f_384_,
    );
    return v___x_386_;
}
pub unsafe fn l_Std_Iter_toHashSet___boxed(
    mut v_00_u03b1_387_: *mut leanh::LeanObject,
    mut v_00_u03b2_388_: *mut leanh::LeanObject,
    mut v_inst_389_: *mut leanh::LeanObject,
    mut v_inst_390_: *mut leanh::LeanObject,
    mut v_inst_391_: *mut leanh::LeanObject,
    mut v_inst_392_: *mut leanh::LeanObject,
    mut v_it_393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_394_ = l_Std_Iter_toHashSet(
        v_00_u03b1_387_,
        v_00_u03b2_388_,
        v_inst_389_,
        v_inst_390_,
        v_inst_391_,
        v_inst_392_,
        v_it_393_,
    );
    leanh::lean_dec(v_inst_391_);
    return v_res_394_;
}
pub unsafe fn l_Std_Iter_Total_toHashSet___redArg(
    mut v_inst_395_: *mut leanh::LeanObject,
    mut v_inst_396_: *mut leanh::LeanObject,
    mut v_inst_397_: *mut leanh::LeanObject,
    mut v_it_398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_399_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_400_ = leanh::lean_alloc_closure(
        l_Std_Iter_toHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_400_, 0, v_inst_395_);
    leanh::lean_closure_set(v___f_400_, 1, v_inst_396_);
    v___x_401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2_once),
        _init_l_Std_Iter_toHashSet___redArg___closed__2,
    );
    v___x_402_ = leanh::lean_apply_6(
        v_inst_397_,
        v___f_399_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_398_,
        v___x_401_,
        v___f_400_,
    );
    return v___x_402_;
}
pub unsafe fn l_Std_Iter_Total_toHashSet(
    mut v_00_u03b1_403_: *mut leanh::LeanObject,
    mut v_00_u03b2_404_: *mut leanh::LeanObject,
    mut v_inst_405_: *mut leanh::LeanObject,
    mut v_inst_406_: *mut leanh::LeanObject,
    mut v_inst_407_: *mut leanh::LeanObject,
    mut v_inst_408_: *mut leanh::LeanObject,
    mut v_inst_409_: *mut leanh::LeanObject,
    mut v_it_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_411_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_412_ = leanh::lean_alloc_closure(
        l_Std_Iter_toHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_412_, 0, v_inst_405_);
    leanh::lean_closure_set(v___f_412_, 1, v_inst_406_);
    v___x_413_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2_once),
        _init_l_Std_Iter_toHashSet___redArg___closed__2,
    );
    v___x_414_ = leanh::lean_apply_6(
        v_inst_409_,
        v___f_411_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_410_,
        v___x_413_,
        v___f_412_,
    );
    return v___x_414_;
}
pub unsafe fn l_Std_Iter_Total_toHashSet___boxed(
    mut v_00_u03b1_415_: *mut leanh::LeanObject,
    mut v_00_u03b2_416_: *mut leanh::LeanObject,
    mut v_inst_417_: *mut leanh::LeanObject,
    mut v_inst_418_: *mut leanh::LeanObject,
    mut v_inst_419_: *mut leanh::LeanObject,
    mut v_inst_420_: *mut leanh::LeanObject,
    mut v_inst_421_: *mut leanh::LeanObject,
    mut v_it_422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_423_ = l_Std_Iter_Total_toHashSet(
        v_00_u03b1_415_,
        v_00_u03b2_416_,
        v_inst_417_,
        v_inst_418_,
        v_inst_419_,
        v_inst_420_,
        v_inst_421_,
        v_it_422_,
    );
    leanh::lean_dec(v_inst_419_);
    return v_res_423_;
}
pub unsafe fn l_Std_Iter_toExtHashSet___redArg___lam__1(
    mut v_inst_424_: *mut leanh::LeanObject,
    mut v_inst_425_: *mut leanh::LeanObject,
    mut v_x1_426_: *mut leanh::LeanObject,
    mut v_x2_427_: *mut leanh::LeanObject,
    mut v_x3_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_429_ = leanh::lean_box(0);
    v___x_430_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_424_,
        v_inst_425_,
        v_x3_428_,
        v_x1_426_,
        v___x_429_,
    );
    v___x_431_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_431_, 0, v___x_430_);
    return v___x_431_;
}
pub unsafe fn l_Std_Iter_toExtHashSet___redArg(
    mut v_inst_432_: *mut leanh::LeanObject,
    mut v_inst_433_: *mut leanh::LeanObject,
    mut v_inst_434_: *mut leanh::LeanObject,
    mut v_it_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_436_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_437_ = leanh::lean_alloc_closure(
        l_Std_Iter_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_437_, 0, v_inst_432_);
    leanh::lean_closure_set(v___f_437_, 1, v_inst_433_);
    v___x_438_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2_once),
        _init_l_Std_Iter_toHashSet___redArg___closed__2,
    );
    v___x_439_ = leanh::lean_apply_6(
        v_inst_434_,
        v___f_436_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_435_,
        v___x_438_,
        v___f_437_,
    );
    return v___x_439_;
}
pub unsafe fn l_Std_Iter_toExtHashSet(
    mut v_00_u03b1_440_: *mut leanh::LeanObject,
    mut v_00_u03b2_441_: *mut leanh::LeanObject,
    mut v_inst_442_: *mut leanh::LeanObject,
    mut v_inst_443_: *mut leanh::LeanObject,
    mut v_inst_444_: *mut leanh::LeanObject,
    mut v_inst_445_: *mut leanh::LeanObject,
    mut v_inst_446_: *mut leanh::LeanObject,
    mut v_inst_447_: *mut leanh::LeanObject,
    mut v_it_448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_449_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_450_ = leanh::lean_alloc_closure(
        l_Std_Iter_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_450_, 0, v_inst_442_);
    leanh::lean_closure_set(v___f_450_, 1, v_inst_443_);
    v___x_451_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2_once),
        _init_l_Std_Iter_toHashSet___redArg___closed__2,
    );
    v___x_452_ = leanh::lean_apply_6(
        v_inst_447_,
        v___f_449_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_448_,
        v___x_451_,
        v___f_450_,
    );
    return v___x_452_;
}
pub unsafe fn l_Std_Iter_toExtHashSet___boxed(
    mut v_00_u03b1_453_: *mut leanh::LeanObject,
    mut v_00_u03b2_454_: *mut leanh::LeanObject,
    mut v_inst_455_: *mut leanh::LeanObject,
    mut v_inst_456_: *mut leanh::LeanObject,
    mut v_inst_457_: *mut leanh::LeanObject,
    mut v_inst_458_: *mut leanh::LeanObject,
    mut v_inst_459_: *mut leanh::LeanObject,
    mut v_inst_460_: *mut leanh::LeanObject,
    mut v_it_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Std_Iter_toExtHashSet(
        v_00_u03b1_453_,
        v_00_u03b2_454_,
        v_inst_455_,
        v_inst_456_,
        v_inst_457_,
        v_inst_458_,
        v_inst_459_,
        v_inst_460_,
        v_it_461_,
    );
    leanh::lean_dec(v_inst_459_);
    return v_res_462_;
}
pub unsafe fn l_Std_Iter_Total_toExtHashSet___redArg(
    mut v_inst_463_: *mut leanh::LeanObject,
    mut v_inst_464_: *mut leanh::LeanObject,
    mut v_inst_465_: *mut leanh::LeanObject,
    mut v_it_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_467_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_468_ = leanh::lean_alloc_closure(
        l_Std_Iter_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_468_, 0, v_inst_463_);
    leanh::lean_closure_set(v___f_468_, 1, v_inst_464_);
    v___x_469_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2_once),
        _init_l_Std_Iter_toHashSet___redArg___closed__2,
    );
    v___x_470_ = leanh::lean_apply_6(
        v_inst_465_,
        v___f_467_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_466_,
        v___x_469_,
        v___f_468_,
    );
    return v___x_470_;
}
pub unsafe fn l_Std_Iter_Total_toExtHashSet(
    mut v_00_u03b1_471_: *mut leanh::LeanObject,
    mut v_00_u03b2_472_: *mut leanh::LeanObject,
    mut v_inst_473_: *mut leanh::LeanObject,
    mut v_inst_474_: *mut leanh::LeanObject,
    mut v_inst_475_: *mut leanh::LeanObject,
    mut v_inst_476_: *mut leanh::LeanObject,
    mut v_inst_477_: *mut leanh::LeanObject,
    mut v_inst_478_: *mut leanh::LeanObject,
    mut v_inst_479_: *mut leanh::LeanObject,
    mut v_it_480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_481_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_482_ = leanh::lean_alloc_closure(
        l_Std_Iter_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_482_, 0, v_inst_473_);
    leanh::lean_closure_set(v___f_482_, 1, v_inst_474_);
    v___x_483_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Iter_toHashSet___redArg___closed__2_once),
        _init_l_Std_Iter_toHashSet___redArg___closed__2,
    );
    v___x_484_ = leanh::lean_apply_6(
        v_inst_479_,
        v___f_481_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_480_,
        v___x_483_,
        v___f_482_,
    );
    return v___x_484_;
}
pub unsafe fn l_Std_Iter_Total_toExtHashSet___boxed(
    mut v_00_u03b1_485_: *mut leanh::LeanObject,
    mut v_00_u03b2_486_: *mut leanh::LeanObject,
    mut v_inst_487_: *mut leanh::LeanObject,
    mut v_inst_488_: *mut leanh::LeanObject,
    mut v_inst_489_: *mut leanh::LeanObject,
    mut v_inst_490_: *mut leanh::LeanObject,
    mut v_inst_491_: *mut leanh::LeanObject,
    mut v_inst_492_: *mut leanh::LeanObject,
    mut v_inst_493_: *mut leanh::LeanObject,
    mut v_it_494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_495_ = l_Std_Iter_Total_toExtHashSet(
        v_00_u03b1_485_,
        v_00_u03b2_486_,
        v_inst_487_,
        v_inst_488_,
        v_inst_489_,
        v_inst_490_,
        v_inst_491_,
        v_inst_492_,
        v_inst_493_,
        v_it_494_,
    );
    leanh::lean_dec(v_inst_491_);
    return v_res_495_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_522_ = l_Std_Iter_toTreeSet___auto__1___closed__10;
    v___x_523_ = l_Lean_mkAtom(v___x_522_);
    return v___x_523_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_524_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__12_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__12,
    );
    v___x_525_ = l_Std_Iter_toTreeSet___auto__1___closed__5;
    v___x_526_ = lean_array_push(v___x_525_, v___x_524_);
    return v___x_526_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_528_ = l_Std_Iter_toTreeSet___auto__1___closed__14;
    v___x_529_ = lean_string_utf8_byte_size(v___x_528_);
    return v___x_529_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_530_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__15_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__15,
    );
    v___x_531_ = leanh::lean_unsigned_to_nat(0);
    v___x_532_ = l_Std_Iter_toTreeSet___auto__1___closed__14;
    v___x_533_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_533_, 0, v___x_532_);
    leanh::lean_ctor_set(v___x_533_, 1, v___x_531_);
    leanh::lean_ctor_set(v___x_533_, 2, v___x_530_);
    return v___x_533_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_536_ = leanh::lean_box(0);
    v___x_537_ = l_Std_Iter_toTreeSet___auto__1___closed__17;
    v___x_538_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__16_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__16,
    );
    v___x_539_ = leanh::lean_box(2);
    v___x_540_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_540_, 0, v___x_539_);
    leanh::lean_ctor_set(v___x_540_, 1, v___x_538_);
    leanh::lean_ctor_set(v___x_540_, 2, v___x_537_);
    leanh::lean_ctor_set(v___x_540_, 3, v___x_536_);
    return v___x_540_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_541_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__18_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__18,
    );
    v___x_542_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__13_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__13,
    );
    v___x_543_ = lean_array_push(v___x_542_, v___x_541_);
    return v___x_543_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__19_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__19,
    );
    v___x_545_ = l_Std_Iter_toTreeSet___auto__1___closed__11;
    v___x_546_ = leanh::lean_box(2);
    v___x_547_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_547_, 0, v___x_546_);
    leanh::lean_ctor_set(v___x_547_, 1, v___x_545_);
    leanh::lean_ctor_set(v___x_547_, 2, v___x_544_);
    return v___x_547_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_548_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__20_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__20,
    );
    v___x_549_ = l_Std_Iter_toTreeSet___auto__1___closed__5;
    v___x_550_ = lean_array_push(v___x_549_, v___x_548_);
    return v___x_550_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__21_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__21,
    );
    v___x_552_ = l_Std_Iter_toTreeSet___auto__1___closed__9;
    v___x_553_ = leanh::lean_box(2);
    v___x_554_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_554_, 0, v___x_553_);
    leanh::lean_ctor_set(v___x_554_, 1, v___x_552_);
    leanh::lean_ctor_set(v___x_554_, 2, v___x_551_);
    return v___x_554_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__22_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__22,
    );
    v___x_556_ = l_Std_Iter_toTreeSet___auto__1___closed__5;
    v___x_557_ = lean_array_push(v___x_556_, v___x_555_);
    return v___x_557_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__23_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__23,
    );
    v___x_559_ = l_Std_Iter_toTreeSet___auto__1___closed__7;
    v___x_560_ = leanh::lean_box(2);
    v___x_561_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_561_, 0, v___x_560_);
    leanh::lean_ctor_set(v___x_561_, 1, v___x_559_);
    leanh::lean_ctor_set(v___x_561_, 2, v___x_558_);
    return v___x_561_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__25() -> *mut leanh::LeanObject {
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_562_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__24_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__24,
    );
    v___x_563_ = l_Std_Iter_toTreeSet___auto__1___closed__5;
    v___x_564_ = lean_array_push(v___x_563_, v___x_562_);
    return v___x_564_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_565_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__25_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__25,
    );
    v___x_566_ = l_Std_Iter_toTreeSet___auto__1___closed__4;
    v___x_567_ = leanh::lean_box(2);
    v___x_568_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
    leanh::lean_ctor_set(v___x_568_, 1, v___x_566_);
    leanh::lean_ctor_set(v___x_568_, 2, v___x_565_);
    return v___x_568_;
}
pub unsafe fn _init_l_Std_Iter_toTreeSet___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_569_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__26_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__26,
    );
    return v___x_569_;
}
pub unsafe fn l_Std_Iter_toTreeSet___redArg___lam__1(
    mut v_cmp_570_: *mut leanh::LeanObject,
    mut v_x1_571_: *mut leanh::LeanObject,
    mut v_x2_572_: *mut leanh::LeanObject,
    mut v_x3_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_574_: u8 = 0;
    leanh::lean_inc(v_x3_573_);
    leanh::lean_inc(v_x1_571_);
    leanh::lean_inc_ref(v_cmp_570_);
    v___x_574_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_570_, v_x1_571_, v_x3_573_);
    if v___x_574_ == 0 {
        let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_575_ = leanh::lean_box(0);
        v___x_576_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_570_, v_x1_571_, v___x_575_, v_x3_573_,
        );
        v___x_577_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_577_, 0, v___x_576_);
        return v___x_577_;
    } else {
        let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x1_571_);
        leanh::lean_dec_ref(v_cmp_570_);
        v___x_578_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_578_, 0, v_x3_573_);
        return v___x_578_;
    }
}
pub unsafe fn l_Std_Iter_toTreeSet___redArg(
    mut v_inst_579_: *mut leanh::LeanObject,
    mut v_it_580_: *mut leanh::LeanObject,
    mut v_cmp_581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_582_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_583_ = leanh::lean_alloc_closure(
        l_Std_Iter_toTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_583_, 0, v_cmp_581_);
    v___x_584_ = leanh::lean_box(1);
    v___x_585_ = leanh::lean_apply_6(
        v_inst_579_,
        v___f_582_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_580_,
        v___x_584_,
        v___f_583_,
    );
    return v___x_585_;
}
pub unsafe fn l_Std_Iter_toTreeSet(
    mut v_00_u03b1_586_: *mut leanh::LeanObject,
    mut v_00_u03b2_587_: *mut leanh::LeanObject,
    mut v_inst_588_: *mut leanh::LeanObject,
    mut v_inst_589_: *mut leanh::LeanObject,
    mut v_it_590_: *mut leanh::LeanObject,
    mut v_cmp_591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_592_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_593_ = leanh::lean_alloc_closure(
        l_Std_Iter_toTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_593_, 0, v_cmp_591_);
    v___x_594_ = leanh::lean_box(1);
    v___x_595_ = leanh::lean_apply_6(
        v_inst_589_,
        v___f_592_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_590_,
        v___x_594_,
        v___f_593_,
    );
    return v___x_595_;
}
pub unsafe fn l_Std_Iter_toTreeSet___boxed(
    mut v_00_u03b1_596_: *mut leanh::LeanObject,
    mut v_00_u03b2_597_: *mut leanh::LeanObject,
    mut v_inst_598_: *mut leanh::LeanObject,
    mut v_inst_599_: *mut leanh::LeanObject,
    mut v_it_600_: *mut leanh::LeanObject,
    mut v_cmp_601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_602_ = l_Std_Iter_toTreeSet(
        v_00_u03b1_596_,
        v_00_u03b2_597_,
        v_inst_598_,
        v_inst_599_,
        v_it_600_,
        v_cmp_601_,
    );
    leanh::lean_dec(v_inst_598_);
    return v_res_602_;
}
pub unsafe fn _init_l_Std_Iter_Total_toTreeSet___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_603_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__26_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__26,
    );
    return v___x_603_;
}
pub unsafe fn l_Std_Iter_Total_toTreeSet___redArg(
    mut v_inst_604_: *mut leanh::LeanObject,
    mut v_it_605_: *mut leanh::LeanObject,
    mut v_cmp_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_607_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_608_ = leanh::lean_alloc_closure(
        l_Std_Iter_toTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_608_, 0, v_cmp_606_);
    v___x_609_ = leanh::lean_box(1);
    v___x_610_ = leanh::lean_apply_6(
        v_inst_604_,
        v___f_607_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_605_,
        v___x_609_,
        v___f_608_,
    );
    return v___x_610_;
}
pub unsafe fn l_Std_Iter_Total_toTreeSet(
    mut v_00_u03b1_611_: *mut leanh::LeanObject,
    mut v_00_u03b2_612_: *mut leanh::LeanObject,
    mut v_inst_613_: *mut leanh::LeanObject,
    mut v_inst_614_: *mut leanh::LeanObject,
    mut v_inst_615_: *mut leanh::LeanObject,
    mut v_it_616_: *mut leanh::LeanObject,
    mut v_cmp_617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_618_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_619_ = leanh::lean_alloc_closure(
        l_Std_Iter_toTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_619_, 0, v_cmp_617_);
    v___x_620_ = leanh::lean_box(1);
    v___x_621_ = leanh::lean_apply_6(
        v_inst_615_,
        v___f_618_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_616_,
        v___x_620_,
        v___f_619_,
    );
    return v___x_621_;
}
pub unsafe fn l_Std_Iter_Total_toTreeSet___boxed(
    mut v_00_u03b1_622_: *mut leanh::LeanObject,
    mut v_00_u03b2_623_: *mut leanh::LeanObject,
    mut v_inst_624_: *mut leanh::LeanObject,
    mut v_inst_625_: *mut leanh::LeanObject,
    mut v_inst_626_: *mut leanh::LeanObject,
    mut v_it_627_: *mut leanh::LeanObject,
    mut v_cmp_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Std_Iter_Total_toTreeSet(
        v_00_u03b1_622_,
        v_00_u03b2_623_,
        v_inst_624_,
        v_inst_625_,
        v_inst_626_,
        v_it_627_,
        v_cmp_628_,
    );
    leanh::lean_dec(v_inst_624_);
    return v_res_629_;
}
pub unsafe fn _init_l_Std_Iter_toExtTreeSet___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_630_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__26_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__26,
    );
    return v___x_630_;
}
pub unsafe fn l_Std_Iter_toExtTreeSet___redArg___lam__1(
    mut v_cmp_631_: *mut leanh::LeanObject,
    mut v_x1_632_: *mut leanh::LeanObject,
    mut v_x2_633_: *mut leanh::LeanObject,
    mut v_x3_634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_635_: u8 = 0;
    leanh::lean_inc(v_x3_634_);
    leanh::lean_inc(v_x1_632_);
    leanh::lean_inc_ref(v_cmp_631_);
    v___x_635_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_631_, v_x1_632_, v_x3_634_);
    if v___x_635_ == 0 {
        let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_636_ = leanh::lean_box(0);
        v___x_637_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
            v_cmp_631_, v_x1_632_, v___x_636_, v_x3_634_,
        );
        v___x_638_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_638_, 0, v___x_637_);
        return v___x_638_;
    } else {
        let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x1_632_);
        leanh::lean_dec_ref(v_cmp_631_);
        v___x_639_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_639_, 0, v_x3_634_);
        return v___x_639_;
    }
}
pub unsafe fn l_Std_Iter_toExtTreeSet___redArg(
    mut v_inst_640_: *mut leanh::LeanObject,
    mut v_it_641_: *mut leanh::LeanObject,
    mut v_cmp_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_643_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_644_ = leanh::lean_alloc_closure(
        l_Std_Iter_toExtTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_644_, 0, v_cmp_642_);
    v___x_645_ = leanh::lean_box(1);
    v___x_646_ = leanh::lean_apply_6(
        v_inst_640_,
        v___f_643_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_641_,
        v___x_645_,
        v___f_644_,
    );
    return v___x_646_;
}
pub unsafe fn l_Std_Iter_toExtTreeSet(
    mut v_00_u03b1_647_: *mut leanh::LeanObject,
    mut v_00_u03b2_648_: *mut leanh::LeanObject,
    mut v_inst_649_: *mut leanh::LeanObject,
    mut v_inst_650_: *mut leanh::LeanObject,
    mut v_it_651_: *mut leanh::LeanObject,
    mut v_cmp_652_: *mut leanh::LeanObject,
    mut v_inst_653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_654_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_655_ = leanh::lean_alloc_closure(
        l_Std_Iter_toExtTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_655_, 0, v_cmp_652_);
    v___x_656_ = leanh::lean_box(1);
    v___x_657_ = leanh::lean_apply_6(
        v_inst_650_,
        v___f_654_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_651_,
        v___x_656_,
        v___f_655_,
    );
    return v___x_657_;
}
pub unsafe fn l_Std_Iter_toExtTreeSet___boxed(
    mut v_00_u03b1_658_: *mut leanh::LeanObject,
    mut v_00_u03b2_659_: *mut leanh::LeanObject,
    mut v_inst_660_: *mut leanh::LeanObject,
    mut v_inst_661_: *mut leanh::LeanObject,
    mut v_it_662_: *mut leanh::LeanObject,
    mut v_cmp_663_: *mut leanh::LeanObject,
    mut v_inst_664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_665_ = l_Std_Iter_toExtTreeSet(
        v_00_u03b1_658_,
        v_00_u03b2_659_,
        v_inst_660_,
        v_inst_661_,
        v_it_662_,
        v_cmp_663_,
        v_inst_664_,
    );
    leanh::lean_dec(v_inst_660_);
    return v_res_665_;
}
pub unsafe fn _init_l_Std_Iter_Total_toExtTreeSet___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_Iter_toTreeSet___auto__1___closed__26_once),
        _init_l_Std_Iter_toTreeSet___auto__1___closed__26,
    );
    return v___x_666_;
}
pub unsafe fn l_Std_Iter_Total_toExtTreeSet___redArg(
    mut v_inst_667_: *mut leanh::LeanObject,
    mut v_it_668_: *mut leanh::LeanObject,
    mut v_cmp_669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_670_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_671_ = leanh::lean_alloc_closure(
        l_Std_Iter_toExtTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_671_, 0, v_cmp_669_);
    v___x_672_ = leanh::lean_box(1);
    v___x_673_ = leanh::lean_apply_6(
        v_inst_667_,
        v___f_670_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_668_,
        v___x_672_,
        v___f_671_,
    );
    return v___x_673_;
}
pub unsafe fn l_Std_Iter_Total_toExtTreeSet(
    mut v_00_u03b1_674_: *mut leanh::LeanObject,
    mut v_00_u03b2_675_: *mut leanh::LeanObject,
    mut v_inst_676_: *mut leanh::LeanObject,
    mut v_inst_677_: *mut leanh::LeanObject,
    mut v_inst_678_: *mut leanh::LeanObject,
    mut v_it_679_: *mut leanh::LeanObject,
    mut v_cmp_680_: *mut leanh::LeanObject,
    mut v_inst_681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_682_ = l_Std_Iter_toHashSet___redArg___closed__0;
    v___f_683_ = leanh::lean_alloc_closure(
        l_Std_Iter_toExtTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_683_, 0, v_cmp_680_);
    v___x_684_ = leanh::lean_box(1);
    v___x_685_ = leanh::lean_apply_6(
        v_inst_678_,
        v___f_682_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_679_,
        v___x_684_,
        v___f_683_,
    );
    return v___x_685_;
}
pub unsafe fn l_Std_Iter_Total_toExtTreeSet___boxed(
    mut v_00_u03b1_686_: *mut leanh::LeanObject,
    mut v_00_u03b2_687_: *mut leanh::LeanObject,
    mut v_inst_688_: *mut leanh::LeanObject,
    mut v_inst_689_: *mut leanh::LeanObject,
    mut v_inst_690_: *mut leanh::LeanObject,
    mut v_it_691_: *mut leanh::LeanObject,
    mut v_cmp_692_: *mut leanh::LeanObject,
    mut v_inst_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Std_Iter_Total_toExtTreeSet(
        v_00_u03b1_686_,
        v_00_u03b2_687_,
        v_inst_688_,
        v_inst_689_,
        v_inst_690_,
        v_it_691_,
        v_cmp_692_,
        v_inst_693_,
    );
    leanh::lean_dec(v_inst_688_);
    return v_res_694_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Consumers_Set(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Consumers_Monadic_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Consumers_Set(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Iter_toTreeSet___auto__1 = _init_l_Std_Iter_toTreeSet___auto__1();
    leanh::lean_mark_persistent(l_Std_Iter_toTreeSet___auto__1);
    l_Std_Iter_Total_toTreeSet___auto__1 = _init_l_Std_Iter_Total_toTreeSet___auto__1();
    leanh::lean_mark_persistent(l_Std_Iter_Total_toTreeSet___auto__1);
    l_Std_Iter_toExtTreeSet___auto__1 = _init_l_Std_Iter_toExtTreeSet___auto__1();
    leanh::lean_mark_persistent(l_Std_Iter_toExtTreeSet___auto__1);
    l_Std_Iter_Total_toExtTreeSet___auto__1 = _init_l_Std_Iter_Total_toExtTreeSet___auto__1();
    leanh::lean_mark_persistent(l_Std_Iter_Total_toExtTreeSet___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Consumers_Set(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Consumers_Monadic_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Consumers_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Consumers_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Consumers_Set(builtin);
}
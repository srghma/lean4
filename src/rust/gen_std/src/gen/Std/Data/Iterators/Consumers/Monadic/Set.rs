// Lean compiler output
// Module: Std.Data.Iterators.Consumers.Monadic.Set
// Imports: Init.Data.Iterators.Consumers.Monadic.Loop Std.Data.HashSet.Basic Std.Data.ExtHashSet.Basic Std.Data.TreeSet.Basic Std.Data.ExtTreeSet.Basic Init.Data.Iterators.Consumers.Monadic.Loop
use crate::ffi::{lean_array_push, lean_mk_array, lean_string_utf8_byte_size};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_contains___redArg;
use crate::r#gen::Std::Data::ExtHashSet::Basic::{
    initialize_Std_Data_ExtHashSet_Basic, runtime_initialize_Std_Data_ExtHashSet_Basic,
};
use crate::r#gen::Std::Data::ExtTreeSet::Basic::{
    initialize_Std_Data_ExtTreeSet_Basic, runtime_initialize_Std_Data_ExtTreeSet_Basic,
};
use crate::r#gen::Std::Data::HashSet::Basic::{
    initialize_Std_Data_HashSet_Basic, runtime_initialize_Std_Data_HashSet_Basic,
};
use crate::r#gen::Std::Data::TreeSet::Basic::{
    initialize_Std_Data_TreeSet_Basic, runtime_initialize_Std_Data_TreeSet_Basic,
};
static mut l_Std_IterM_toHashSet___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toHashSet___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toHashSet___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toHashSet___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__2_value: leanh::LeanStringObject<7> =
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
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__3_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
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
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
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
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__6_value: leanh::LeanStringObject<
    19,
> = leanh::LeanStringObject {
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
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__10_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
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
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__14_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
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
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_IterM_toExtTreeSet___auto__1___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16710690322389477741 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toExtTreeSet___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_IterM_toExtTreeSet___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_IterM_toExtTreeSet___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_IterM_Total_toExtTreeSet___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_IterM_toHashSet___redArg___lam__0(
    mut v_toBind_481_: *mut leanh::LeanObject,
    mut v_x_482_: *mut leanh::LeanObject,
    mut v_x_483_: *mut leanh::LeanObject,
    mut v_f_484_: *mut leanh::LeanObject,
    mut v_x_485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = leanh::lean_apply_4(
        v_toBind_481_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_485_,
        v_f_484_,
    );
    return v___x_486_;
}
pub unsafe fn l_Std_IterM_toHashSet___redArg___lam__1(
    mut v_toPure_487_: *mut leanh::LeanObject,
    mut v_____do__lift_488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = leanh::lean_apply_2(
        v_toPure_487_,
        leanh::lean_box(0),
        v_____do__lift_488_,
    );
    return v___x_489_;
}
pub unsafe fn l_Std_IterM_toHashSet___redArg___lam__2(
    mut v_inst_490_: *mut leanh::LeanObject,
    mut v_inst_491_: *mut leanh::LeanObject,
    mut v_toPure_492_: *mut leanh::LeanObject,
    mut v_toBind_493_: *mut leanh::LeanObject,
    mut v___f_494_: *mut leanh::LeanObject,
    mut v_x1_495_: *mut leanh::LeanObject,
    mut v_x2_496_: *mut leanh::LeanObject,
    mut v_x3_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ = leanh::lean_box(0);
    v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_490_,
        v_inst_491_,
        v_x3_497_,
        v_x1_495_,
        v___x_498_,
    );
    v___x_500_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_500_, 0, v___x_499_);
    v___x_501_ = leanh::lean_apply_2(v_toPure_492_, leanh::lean_box(0), v___x_500_);
    v___x_502_ = leanh::lean_apply_4(
        v_toBind_493_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_501_,
        v___f_494_,
    );
    return v___x_502_;
}
pub unsafe fn _init_l_Std_IterM_toHashSet___redArg___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_503_ = leanh::lean_box(0);
    v___x_504_ = leanh::lean_unsigned_to_nat(16);
    v___x_505_ = lean_mk_array(v___x_504_, v___x_503_);
    return v___x_505_;
}
pub unsafe fn _init_l_Std_IterM_toHashSet___redArg___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__0_once),
        _init_l_Std_IterM_toHashSet___redArg___closed__0,
    );
    v___x_507_ = leanh::lean_unsigned_to_nat(0);
    v___x_508_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_508_, 0, v___x_507_);
    leanh::lean_ctor_set(v___x_508_, 1, v___x_506_);
    return v___x_508_;
}
pub unsafe fn l_Std_IterM_toHashSet___redArg(
    mut v_inst_509_: *mut leanh::LeanObject,
    mut v_inst_510_: *mut leanh::LeanObject,
    mut v_inst_511_: *mut leanh::LeanObject,
    mut v_inst_512_: *mut leanh::LeanObject,
    mut v_it_513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_514_ = leanh::lean_ctor_get(v_inst_511_, 0);
    leanh::lean_inc_ref(v_toApplicative_514_);
    v_toBind_515_ = leanh::lean_ctor_get(v_inst_511_, 1);
    leanh::lean_inc_n(v_toBind_515_, 2);
    leanh::lean_dec_ref(v_inst_511_);
    v_toPure_516_ = leanh::lean_ctor_get(v_toApplicative_514_, 1);
    leanh::lean_inc_n(v_toPure_516_, 2);
    leanh::lean_dec_ref(v_toApplicative_514_);
    v___x_517_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1_once),
        _init_l_Std_IterM_toHashSet___redArg___closed__1,
    );
    v___f_518_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_518_, 0, v_toBind_515_);
    v___f_519_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_519_, 0, v_toPure_516_);
    v___f_520_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_520_, 0, v_inst_509_);
    leanh::lean_closure_set(v___f_520_, 1, v_inst_510_);
    leanh::lean_closure_set(v___f_520_, 2, v_toPure_516_);
    leanh::lean_closure_set(v___f_520_, 3, v_toBind_515_);
    leanh::lean_closure_set(v___f_520_, 4, v___f_519_);
    v___x_521_ = leanh::lean_apply_6(
        v_inst_512_,
        v___f_518_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_513_,
        v___x_517_,
        v___f_520_,
    );
    return v___x_521_;
}
pub unsafe fn l_Std_IterM_toHashSet(
    mut v_00_u03b1_522_: *mut leanh::LeanObject,
    mut v_00_u03b2_523_: *mut leanh::LeanObject,
    mut v_inst_524_: *mut leanh::LeanObject,
    mut v_inst_525_: *mut leanh::LeanObject,
    mut v_m_526_: *mut leanh::LeanObject,
    mut v_inst_527_: *mut leanh::LeanObject,
    mut v_inst_528_: *mut leanh::LeanObject,
    mut v_inst_529_: *mut leanh::LeanObject,
    mut v_it_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_531_ = leanh::lean_ctor_get(v_inst_527_, 0);
    leanh::lean_inc_ref(v_toApplicative_531_);
    v_toBind_532_ = leanh::lean_ctor_get(v_inst_527_, 1);
    leanh::lean_inc_n(v_toBind_532_, 2);
    leanh::lean_dec_ref(v_inst_527_);
    v_toPure_533_ = leanh::lean_ctor_get(v_toApplicative_531_, 1);
    leanh::lean_inc_n(v_toPure_533_, 2);
    leanh::lean_dec_ref(v_toApplicative_531_);
    v___x_534_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1_once),
        _init_l_Std_IterM_toHashSet___redArg___closed__1,
    );
    v___f_535_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_535_, 0, v_toBind_532_);
    v___f_536_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_536_, 0, v_toPure_533_);
    v___f_537_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_537_, 0, v_inst_524_);
    leanh::lean_closure_set(v___f_537_, 1, v_inst_525_);
    leanh::lean_closure_set(v___f_537_, 2, v_toPure_533_);
    leanh::lean_closure_set(v___f_537_, 3, v_toBind_532_);
    leanh::lean_closure_set(v___f_537_, 4, v___f_536_);
    v___x_538_ = leanh::lean_apply_6(
        v_inst_529_,
        v___f_535_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_530_,
        v___x_534_,
        v___f_537_,
    );
    return v___x_538_;
}
pub unsafe fn l_Std_IterM_toHashSet___boxed(
    mut v_00_u03b1_539_: *mut leanh::LeanObject,
    mut v_00_u03b2_540_: *mut leanh::LeanObject,
    mut v_inst_541_: *mut leanh::LeanObject,
    mut v_inst_542_: *mut leanh::LeanObject,
    mut v_m_543_: *mut leanh::LeanObject,
    mut v_inst_544_: *mut leanh::LeanObject,
    mut v_inst_545_: *mut leanh::LeanObject,
    mut v_inst_546_: *mut leanh::LeanObject,
    mut v_it_547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_548_ = l_Std_IterM_toHashSet(
        v_00_u03b1_539_,
        v_00_u03b2_540_,
        v_inst_541_,
        v_inst_542_,
        v_m_543_,
        v_inst_544_,
        v_inst_545_,
        v_inst_546_,
        v_it_547_,
    );
    leanh::lean_dec(v_inst_545_);
    return v_res_548_;
}
pub unsafe fn l_Std_IterM_Total_toHashSet___redArg(
    mut v_inst_549_: *mut leanh::LeanObject,
    mut v_inst_550_: *mut leanh::LeanObject,
    mut v_inst_551_: *mut leanh::LeanObject,
    mut v_inst_552_: *mut leanh::LeanObject,
    mut v_it_553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_554_ = leanh::lean_ctor_get(v_inst_551_, 0);
    leanh::lean_inc_ref(v_toApplicative_554_);
    v_toBind_555_ = leanh::lean_ctor_get(v_inst_551_, 1);
    leanh::lean_inc_n(v_toBind_555_, 2);
    leanh::lean_dec_ref(v_inst_551_);
    v_toPure_556_ = leanh::lean_ctor_get(v_toApplicative_554_, 1);
    leanh::lean_inc_n(v_toPure_556_, 2);
    leanh::lean_dec_ref(v_toApplicative_554_);
    v___x_557_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1_once),
        _init_l_Std_IterM_toHashSet___redArg___closed__1,
    );
    v___f_558_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_558_, 0, v_toBind_555_);
    v___f_559_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_559_, 0, v_toPure_556_);
    v___f_560_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_560_, 0, v_inst_549_);
    leanh::lean_closure_set(v___f_560_, 1, v_inst_550_);
    leanh::lean_closure_set(v___f_560_, 2, v_toPure_556_);
    leanh::lean_closure_set(v___f_560_, 3, v_toBind_555_);
    leanh::lean_closure_set(v___f_560_, 4, v___f_559_);
    v___x_561_ = leanh::lean_apply_6(
        v_inst_552_,
        v___f_558_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_553_,
        v___x_557_,
        v___f_560_,
    );
    return v___x_561_;
}
pub unsafe fn l_Std_IterM_Total_toHashSet(
    mut v_00_u03b1_562_: *mut leanh::LeanObject,
    mut v_00_u03b2_563_: *mut leanh::LeanObject,
    mut v_inst_564_: *mut leanh::LeanObject,
    mut v_inst_565_: *mut leanh::LeanObject,
    mut v_m_566_: *mut leanh::LeanObject,
    mut v_inst_567_: *mut leanh::LeanObject,
    mut v_inst_568_: *mut leanh::LeanObject,
    mut v_inst_569_: *mut leanh::LeanObject,
    mut v_inst_570_: *mut leanh::LeanObject,
    mut v_it_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_572_ = leanh::lean_ctor_get(v_inst_567_, 0);
    leanh::lean_inc_ref(v_toApplicative_572_);
    v_toBind_573_ = leanh::lean_ctor_get(v_inst_567_, 1);
    leanh::lean_inc_n(v_toBind_573_, 2);
    leanh::lean_dec_ref(v_inst_567_);
    v_toPure_574_ = leanh::lean_ctor_get(v_toApplicative_572_, 1);
    leanh::lean_inc_n(v_toPure_574_, 2);
    leanh::lean_dec_ref(v_toApplicative_572_);
    v___x_575_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1_once),
        _init_l_Std_IterM_toHashSet___redArg___closed__1,
    );
    v___f_576_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_576_, 0, v_toBind_573_);
    v___f_577_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_577_, 0, v_toPure_574_);
    v___f_578_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_578_, 0, v_inst_564_);
    leanh::lean_closure_set(v___f_578_, 1, v_inst_565_);
    leanh::lean_closure_set(v___f_578_, 2, v_toPure_574_);
    leanh::lean_closure_set(v___f_578_, 3, v_toBind_573_);
    leanh::lean_closure_set(v___f_578_, 4, v___f_577_);
    v___x_579_ = leanh::lean_apply_6(
        v_inst_570_,
        v___f_576_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_571_,
        v___x_575_,
        v___f_578_,
    );
    return v___x_579_;
}
pub unsafe fn l_Std_IterM_Total_toHashSet___boxed(
    mut v_00_u03b1_580_: *mut leanh::LeanObject,
    mut v_00_u03b2_581_: *mut leanh::LeanObject,
    mut v_inst_582_: *mut leanh::LeanObject,
    mut v_inst_583_: *mut leanh::LeanObject,
    mut v_m_584_: *mut leanh::LeanObject,
    mut v_inst_585_: *mut leanh::LeanObject,
    mut v_inst_586_: *mut leanh::LeanObject,
    mut v_inst_587_: *mut leanh::LeanObject,
    mut v_inst_588_: *mut leanh::LeanObject,
    mut v_it_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_590_ = l_Std_IterM_Total_toHashSet(
        v_00_u03b1_580_,
        v_00_u03b2_581_,
        v_inst_582_,
        v_inst_583_,
        v_m_584_,
        v_inst_585_,
        v_inst_586_,
        v_inst_587_,
        v_inst_588_,
        v_it_589_,
    );
    leanh::lean_dec(v_inst_586_);
    return v_res_590_;
}
pub unsafe fn l_Std_IterM_toExtHashSet___redArg___lam__1(
    mut v_toPure_591_: *mut leanh::LeanObject,
    mut v_____do__lift_592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_593_ = leanh::lean_apply_2(
        v_toPure_591_,
        leanh::lean_box(0),
        v_____do__lift_592_,
    );
    return v___x_593_;
}
pub unsafe fn l_Std_IterM_toExtHashSet___redArg___lam__0(
    mut v_inst_594_: *mut leanh::LeanObject,
    mut v_inst_595_: *mut leanh::LeanObject,
    mut v_toPure_596_: *mut leanh::LeanObject,
    mut v_toBind_597_: *mut leanh::LeanObject,
    mut v___f_598_: *mut leanh::LeanObject,
    mut v_x1_599_: *mut leanh::LeanObject,
    mut v_x2_600_: *mut leanh::LeanObject,
    mut v_x3_601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = leanh::lean_box(0);
    v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_inst_594_,
        v_inst_595_,
        v_x3_601_,
        v_x1_599_,
        v___x_602_,
    );
    v___x_604_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_604_, 0, v___x_603_);
    v___x_605_ = leanh::lean_apply_2(v_toPure_596_, leanh::lean_box(0), v___x_604_);
    v___x_606_ = leanh::lean_apply_4(
        v_toBind_597_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_605_,
        v___f_598_,
    );
    return v___x_606_;
}
pub unsafe fn l_Std_IterM_toExtHashSet___redArg(
    mut v_inst_607_: *mut leanh::LeanObject,
    mut v_inst_608_: *mut leanh::LeanObject,
    mut v_inst_609_: *mut leanh::LeanObject,
    mut v_inst_610_: *mut leanh::LeanObject,
    mut v_it_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_612_ = leanh::lean_ctor_get(v_inst_609_, 0);
    leanh::lean_inc_ref(v_toApplicative_612_);
    v_toBind_613_ = leanh::lean_ctor_get(v_inst_609_, 1);
    leanh::lean_inc_n(v_toBind_613_, 2);
    leanh::lean_dec_ref(v_inst_609_);
    v_toPure_614_ = leanh::lean_ctor_get(v_toApplicative_612_, 1);
    leanh::lean_inc_n(v_toPure_614_, 2);
    leanh::lean_dec_ref(v_toApplicative_612_);
    v___x_615_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1_once),
        _init_l_Std_IterM_toHashSet___redArg___closed__1,
    );
    v___f_616_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_616_, 0, v_toBind_613_);
    v___f_617_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_617_, 0, v_toPure_614_);
    v___f_618_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_618_, 0, v_inst_607_);
    leanh::lean_closure_set(v___f_618_, 1, v_inst_608_);
    leanh::lean_closure_set(v___f_618_, 2, v_toPure_614_);
    leanh::lean_closure_set(v___f_618_, 3, v_toBind_613_);
    leanh::lean_closure_set(v___f_618_, 4, v___f_617_);
    v___x_619_ = leanh::lean_apply_6(
        v_inst_610_,
        v___f_616_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_611_,
        v___x_615_,
        v___f_618_,
    );
    return v___x_619_;
}
pub unsafe fn l_Std_IterM_toExtHashSet(
    mut v_00_u03b1_620_: *mut leanh::LeanObject,
    mut v_00_u03b2_621_: *mut leanh::LeanObject,
    mut v_inst_622_: *mut leanh::LeanObject,
    mut v_inst_623_: *mut leanh::LeanObject,
    mut v_inst_624_: *mut leanh::LeanObject,
    mut v_inst_625_: *mut leanh::LeanObject,
    mut v_m_626_: *mut leanh::LeanObject,
    mut v_inst_627_: *mut leanh::LeanObject,
    mut v_inst_628_: *mut leanh::LeanObject,
    mut v_inst_629_: *mut leanh::LeanObject,
    mut v_it_630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_631_ = leanh::lean_ctor_get(v_inst_627_, 0);
    leanh::lean_inc_ref(v_toApplicative_631_);
    v_toBind_632_ = leanh::lean_ctor_get(v_inst_627_, 1);
    leanh::lean_inc_n(v_toBind_632_, 2);
    leanh::lean_dec_ref(v_inst_627_);
    v_toPure_633_ = leanh::lean_ctor_get(v_toApplicative_631_, 1);
    leanh::lean_inc_n(v_toPure_633_, 2);
    leanh::lean_dec_ref(v_toApplicative_631_);
    v___x_634_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1_once),
        _init_l_Std_IterM_toHashSet___redArg___closed__1,
    );
    v___f_635_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_635_, 0, v_toBind_632_);
    v___f_636_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_636_, 0, v_toPure_633_);
    v___f_637_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_637_, 0, v_inst_622_);
    leanh::lean_closure_set(v___f_637_, 1, v_inst_623_);
    leanh::lean_closure_set(v___f_637_, 2, v_toPure_633_);
    leanh::lean_closure_set(v___f_637_, 3, v_toBind_632_);
    leanh::lean_closure_set(v___f_637_, 4, v___f_636_);
    v___x_638_ = leanh::lean_apply_6(
        v_inst_629_,
        v___f_635_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_630_,
        v___x_634_,
        v___f_637_,
    );
    return v___x_638_;
}
pub unsafe fn l_Std_IterM_toExtHashSet___boxed(
    mut v_00_u03b1_639_: *mut leanh::LeanObject,
    mut v_00_u03b2_640_: *mut leanh::LeanObject,
    mut v_inst_641_: *mut leanh::LeanObject,
    mut v_inst_642_: *mut leanh::LeanObject,
    mut v_inst_643_: *mut leanh::LeanObject,
    mut v_inst_644_: *mut leanh::LeanObject,
    mut v_m_645_: *mut leanh::LeanObject,
    mut v_inst_646_: *mut leanh::LeanObject,
    mut v_inst_647_: *mut leanh::LeanObject,
    mut v_inst_648_: *mut leanh::LeanObject,
    mut v_it_649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_650_ = l_Std_IterM_toExtHashSet(
        v_00_u03b1_639_,
        v_00_u03b2_640_,
        v_inst_641_,
        v_inst_642_,
        v_inst_643_,
        v_inst_644_,
        v_m_645_,
        v_inst_646_,
        v_inst_647_,
        v_inst_648_,
        v_it_649_,
    );
    leanh::lean_dec(v_inst_647_);
    return v_res_650_;
}
pub unsafe fn l_Std_IterM_Total_toExtHashSet___redArg(
    mut v_inst_651_: *mut leanh::LeanObject,
    mut v_inst_652_: *mut leanh::LeanObject,
    mut v_inst_653_: *mut leanh::LeanObject,
    mut v_inst_654_: *mut leanh::LeanObject,
    mut v_it_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_656_ = leanh::lean_ctor_get(v_inst_653_, 0);
    leanh::lean_inc_ref(v_toApplicative_656_);
    v_toBind_657_ = leanh::lean_ctor_get(v_inst_653_, 1);
    leanh::lean_inc_n(v_toBind_657_, 2);
    leanh::lean_dec_ref(v_inst_653_);
    v_toPure_658_ = leanh::lean_ctor_get(v_toApplicative_656_, 1);
    leanh::lean_inc_n(v_toPure_658_, 2);
    leanh::lean_dec_ref(v_toApplicative_656_);
    v___x_659_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1_once),
        _init_l_Std_IterM_toHashSet___redArg___closed__1,
    );
    v___f_660_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_660_, 0, v_toBind_657_);
    v___f_661_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_661_, 0, v_toPure_658_);
    v___f_662_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_662_, 0, v_inst_651_);
    leanh::lean_closure_set(v___f_662_, 1, v_inst_652_);
    leanh::lean_closure_set(v___f_662_, 2, v_toPure_658_);
    leanh::lean_closure_set(v___f_662_, 3, v_toBind_657_);
    leanh::lean_closure_set(v___f_662_, 4, v___f_661_);
    v___x_663_ = leanh::lean_apply_6(
        v_inst_654_,
        v___f_660_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_655_,
        v___x_659_,
        v___f_662_,
    );
    return v___x_663_;
}
pub unsafe fn l_Std_IterM_Total_toExtHashSet(
    mut v_00_u03b1_664_: *mut leanh::LeanObject,
    mut v_00_u03b2_665_: *mut leanh::LeanObject,
    mut v_inst_666_: *mut leanh::LeanObject,
    mut v_inst_667_: *mut leanh::LeanObject,
    mut v_inst_668_: *mut leanh::LeanObject,
    mut v_inst_669_: *mut leanh::LeanObject,
    mut v_m_670_: *mut leanh::LeanObject,
    mut v_inst_671_: *mut leanh::LeanObject,
    mut v_inst_672_: *mut leanh::LeanObject,
    mut v_inst_673_: *mut leanh::LeanObject,
    mut v_inst_674_: *mut leanh::LeanObject,
    mut v_it_675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_676_ = leanh::lean_ctor_get(v_inst_671_, 0);
    leanh::lean_inc_ref(v_toApplicative_676_);
    v_toBind_677_ = leanh::lean_ctor_get(v_inst_671_, 1);
    leanh::lean_inc_n(v_toBind_677_, 2);
    leanh::lean_dec_ref(v_inst_671_);
    v_toPure_678_ = leanh::lean_ctor_get(v_toApplicative_676_, 1);
    leanh::lean_inc_n(v_toPure_678_, 2);
    leanh::lean_dec_ref(v_toApplicative_676_);
    v___x_679_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_IterM_toHashSet___redArg___closed__1_once),
        _init_l_Std_IterM_toHashSet___redArg___closed__1,
    );
    v___f_680_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_680_, 0, v_toBind_677_);
    v___f_681_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_681_, 0, v_toPure_678_);
    v___f_682_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_682_, 0, v_inst_666_);
    leanh::lean_closure_set(v___f_682_, 1, v_inst_667_);
    leanh::lean_closure_set(v___f_682_, 2, v_toPure_678_);
    leanh::lean_closure_set(v___f_682_, 3, v_toBind_677_);
    leanh::lean_closure_set(v___f_682_, 4, v___f_681_);
    v___x_683_ = leanh::lean_apply_6(
        v_inst_674_,
        v___f_680_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_675_,
        v___x_679_,
        v___f_682_,
    );
    return v___x_683_;
}
pub unsafe fn l_Std_IterM_Total_toExtHashSet___boxed(
    mut v_00_u03b1_684_: *mut leanh::LeanObject,
    mut v_00_u03b2_685_: *mut leanh::LeanObject,
    mut v_inst_686_: *mut leanh::LeanObject,
    mut v_inst_687_: *mut leanh::LeanObject,
    mut v_inst_688_: *mut leanh::LeanObject,
    mut v_inst_689_: *mut leanh::LeanObject,
    mut v_m_690_: *mut leanh::LeanObject,
    mut v_inst_691_: *mut leanh::LeanObject,
    mut v_inst_692_: *mut leanh::LeanObject,
    mut v_inst_693_: *mut leanh::LeanObject,
    mut v_inst_694_: *mut leanh::LeanObject,
    mut v_it_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Std_IterM_Total_toExtHashSet(
        v_00_u03b1_684_,
        v_00_u03b2_685_,
        v_inst_686_,
        v_inst_687_,
        v_inst_688_,
        v_inst_689_,
        v_m_690_,
        v_inst_691_,
        v_inst_692_,
        v_inst_693_,
        v_inst_694_,
        v_it_695_,
    );
    leanh::lean_dec(v_inst_692_);
    return v_res_696_;
}
pub unsafe fn l_Std_IterM_toTreeSet___redArg___lam__1(
    mut v_toPure_697_: *mut leanh::LeanObject,
    mut v_____do__lift_698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = leanh::lean_apply_2(
        v_toPure_697_,
        leanh::lean_box(0),
        v_____do__lift_698_,
    );
    return v___x_699_;
}
pub unsafe fn l_Std_IterM_toTreeSet___redArg___lam__0(
    mut v_toPure_700_: *mut leanh::LeanObject,
    mut v_toBind_701_: *mut leanh::LeanObject,
    mut v___f_702_: *mut leanh::LeanObject,
    mut v_cmp_703_: *mut leanh::LeanObject,
    mut v_x1_704_: *mut leanh::LeanObject,
    mut v_x2_705_: *mut leanh::LeanObject,
    mut v_x3_706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: u8 = 0;
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_x3_706_);
                leanh::lean_inc(v_x1_704_);
                leanh::lean_inc_ref(v_cmp_703_);
                v___x_712_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(
                    v_cmp_703_, v_x1_704_, v_x3_706_,
                );
                if v___x_712_ == 0 {
                    v___x_713_ = leanh::lean_box(0);
                    v___x_714_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_703_, v_x1_704_, v___x_713_, v_x3_706_,
                    );
                    v___y_708_ = v___x_714_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_x1_704_);
                    leanh::lean_dec_ref(v_cmp_703_);
                    v___y_708_ = v_x3_706_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_709_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_709_, 0, v___y_708_);
                v___x_710_ = leanh::lean_apply_2(
                    v_toPure_700_,
                    leanh::lean_box(0),
                    v___x_709_,
                );
                v___x_711_ = leanh::lean_apply_4(
                    v_toBind_701_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_710_,
                    v___f_702_,
                );
                return v___x_711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterM_toTreeSet___redArg(
    mut v_inst_715_: *mut leanh::LeanObject,
    mut v_inst_716_: *mut leanh::LeanObject,
    mut v_it_717_: *mut leanh::LeanObject,
    mut v_cmp_718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_719_ = leanh::lean_ctor_get(v_inst_715_, 0);
    leanh::lean_inc_ref(v_toApplicative_719_);
    v_toBind_720_ = leanh::lean_ctor_get(v_inst_715_, 1);
    leanh::lean_inc_n(v_toBind_720_, 2);
    leanh::lean_dec_ref(v_inst_715_);
    v_toPure_721_ = leanh::lean_ctor_get(v_toApplicative_719_, 1);
    leanh::lean_inc_n(v_toPure_721_, 2);
    leanh::lean_dec_ref(v_toApplicative_719_);
    v___x_722_ = leanh::lean_box(1);
    v___f_723_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_723_, 0, v_toBind_720_);
    v___f_724_ = leanh::lean_alloc_closure(
        l_Std_IterM_toTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_724_, 0, v_toPure_721_);
    v___f_725_ = leanh::lean_alloc_closure(
        l_Std_IterM_toTreeSet___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_725_, 0, v_toPure_721_);
    leanh::lean_closure_set(v___f_725_, 1, v_toBind_720_);
    leanh::lean_closure_set(v___f_725_, 2, v___f_724_);
    leanh::lean_closure_set(v___f_725_, 3, v_cmp_718_);
    v___x_726_ = leanh::lean_apply_6(
        v_inst_716_,
        v___f_723_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_717_,
        v___x_722_,
        v___f_725_,
    );
    return v___x_726_;
}
pub unsafe fn l_Std_IterM_toTreeSet(
    mut v_00_u03b1_727_: *mut leanh::LeanObject,
    mut v_00_u03b2_728_: *mut leanh::LeanObject,
    mut v_m_729_: *mut leanh::LeanObject,
    mut v_inst_730_: *mut leanh::LeanObject,
    mut v_inst_731_: *mut leanh::LeanObject,
    mut v_inst_732_: *mut leanh::LeanObject,
    mut v_it_733_: *mut leanh::LeanObject,
    mut v_cmp_734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_735_ = leanh::lean_ctor_get(v_inst_730_, 0);
    leanh::lean_inc_ref(v_toApplicative_735_);
    v_toBind_736_ = leanh::lean_ctor_get(v_inst_730_, 1);
    leanh::lean_inc_n(v_toBind_736_, 2);
    leanh::lean_dec_ref(v_inst_730_);
    v_toPure_737_ = leanh::lean_ctor_get(v_toApplicative_735_, 1);
    leanh::lean_inc_n(v_toPure_737_, 2);
    leanh::lean_dec_ref(v_toApplicative_735_);
    v___x_738_ = leanh::lean_box(1);
    v___f_739_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_739_, 0, v_toBind_736_);
    v___f_740_ = leanh::lean_alloc_closure(
        l_Std_IterM_toTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_740_, 0, v_toPure_737_);
    v___f_741_ = leanh::lean_alloc_closure(
        l_Std_IterM_toTreeSet___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_741_, 0, v_toPure_737_);
    leanh::lean_closure_set(v___f_741_, 1, v_toBind_736_);
    leanh::lean_closure_set(v___f_741_, 2, v___f_740_);
    leanh::lean_closure_set(v___f_741_, 3, v_cmp_734_);
    v___x_742_ = leanh::lean_apply_6(
        v_inst_732_,
        v___f_739_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_733_,
        v___x_738_,
        v___f_741_,
    );
    return v___x_742_;
}
pub unsafe fn l_Std_IterM_toTreeSet___boxed(
    mut v_00_u03b1_743_: *mut leanh::LeanObject,
    mut v_00_u03b2_744_: *mut leanh::LeanObject,
    mut v_m_745_: *mut leanh::LeanObject,
    mut v_inst_746_: *mut leanh::LeanObject,
    mut v_inst_747_: *mut leanh::LeanObject,
    mut v_inst_748_: *mut leanh::LeanObject,
    mut v_it_749_: *mut leanh::LeanObject,
    mut v_cmp_750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_751_ = l_Std_IterM_toTreeSet(
        v_00_u03b1_743_,
        v_00_u03b2_744_,
        v_m_745_,
        v_inst_746_,
        v_inst_747_,
        v_inst_748_,
        v_it_749_,
        v_cmp_750_,
    );
    leanh::lean_dec(v_inst_747_);
    return v_res_751_;
}
pub unsafe fn l_Std_IterM_Total_toTreeSet___redArg(
    mut v_inst_752_: *mut leanh::LeanObject,
    mut v_inst_753_: *mut leanh::LeanObject,
    mut v_it_754_: *mut leanh::LeanObject,
    mut v_cmp_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_756_ = leanh::lean_ctor_get(v_inst_752_, 0);
    leanh::lean_inc_ref(v_toApplicative_756_);
    v_toBind_757_ = leanh::lean_ctor_get(v_inst_752_, 1);
    leanh::lean_inc_n(v_toBind_757_, 2);
    leanh::lean_dec_ref(v_inst_752_);
    v_toPure_758_ = leanh::lean_ctor_get(v_toApplicative_756_, 1);
    leanh::lean_inc_n(v_toPure_758_, 2);
    leanh::lean_dec_ref(v_toApplicative_756_);
    v___x_759_ = leanh::lean_box(1);
    v___f_760_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_760_, 0, v_toBind_757_);
    v___f_761_ = leanh::lean_alloc_closure(
        l_Std_IterM_toTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_761_, 0, v_toPure_758_);
    v___f_762_ = leanh::lean_alloc_closure(
        l_Std_IterM_toTreeSet___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_762_, 0, v_toPure_758_);
    leanh::lean_closure_set(v___f_762_, 1, v_toBind_757_);
    leanh::lean_closure_set(v___f_762_, 2, v___f_761_);
    leanh::lean_closure_set(v___f_762_, 3, v_cmp_755_);
    v___x_763_ = leanh::lean_apply_6(
        v_inst_753_,
        v___f_760_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_754_,
        v___x_759_,
        v___f_762_,
    );
    return v___x_763_;
}
pub unsafe fn l_Std_IterM_Total_toTreeSet(
    mut v_00_u03b1_764_: *mut leanh::LeanObject,
    mut v_00_u03b2_765_: *mut leanh::LeanObject,
    mut v_m_766_: *mut leanh::LeanObject,
    mut v_inst_767_: *mut leanh::LeanObject,
    mut v_inst_768_: *mut leanh::LeanObject,
    mut v_inst_769_: *mut leanh::LeanObject,
    mut v_inst_770_: *mut leanh::LeanObject,
    mut v_it_771_: *mut leanh::LeanObject,
    mut v_cmp_772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_773_ = leanh::lean_ctor_get(v_inst_767_, 0);
    leanh::lean_inc_ref(v_toApplicative_773_);
    v_toBind_774_ = leanh::lean_ctor_get(v_inst_767_, 1);
    leanh::lean_inc_n(v_toBind_774_, 2);
    leanh::lean_dec_ref(v_inst_767_);
    v_toPure_775_ = leanh::lean_ctor_get(v_toApplicative_773_, 1);
    leanh::lean_inc_n(v_toPure_775_, 2);
    leanh::lean_dec_ref(v_toApplicative_773_);
    v___x_776_ = leanh::lean_box(1);
    v___f_777_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_777_, 0, v_toBind_774_);
    v___f_778_ = leanh::lean_alloc_closure(
        l_Std_IterM_toTreeSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_778_, 0, v_toPure_775_);
    v___f_779_ = leanh::lean_alloc_closure(
        l_Std_IterM_toTreeSet___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_779_, 0, v_toPure_775_);
    leanh::lean_closure_set(v___f_779_, 1, v_toBind_774_);
    leanh::lean_closure_set(v___f_779_, 2, v___f_778_);
    leanh::lean_closure_set(v___f_779_, 3, v_cmp_772_);
    v___x_780_ = leanh::lean_apply_6(
        v_inst_770_,
        v___f_777_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_771_,
        v___x_776_,
        v___f_779_,
    );
    return v___x_780_;
}
pub unsafe fn l_Std_IterM_Total_toTreeSet___boxed(
    mut v_00_u03b1_781_: *mut leanh::LeanObject,
    mut v_00_u03b2_782_: *mut leanh::LeanObject,
    mut v_m_783_: *mut leanh::LeanObject,
    mut v_inst_784_: *mut leanh::LeanObject,
    mut v_inst_785_: *mut leanh::LeanObject,
    mut v_inst_786_: *mut leanh::LeanObject,
    mut v_inst_787_: *mut leanh::LeanObject,
    mut v_it_788_: *mut leanh::LeanObject,
    mut v_cmp_789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Std_IterM_Total_toTreeSet(
        v_00_u03b1_781_,
        v_00_u03b2_782_,
        v_m_783_,
        v_inst_784_,
        v_inst_785_,
        v_inst_786_,
        v_inst_787_,
        v_it_788_,
        v_cmp_789_,
    );
    leanh::lean_dec(v_inst_785_);
    return v_res_790_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_817_ = l_Std_IterM_toExtTreeSet___auto__1___closed__10;
    v___x_818_ = l_Lean_mkAtom(v___x_817_);
    return v___x_818_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__12_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__12,
    );
    v___x_820_ = l_Std_IterM_toExtTreeSet___auto__1___closed__5;
    v___x_821_ = lean_array_push(v___x_820_, v___x_819_);
    return v___x_821_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ = l_Std_IterM_toExtTreeSet___auto__1___closed__14;
    v___x_824_ = lean_string_utf8_byte_size(v___x_823_);
    return v___x_824_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_825_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__15_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__15,
    );
    v___x_826_ = leanh::lean_unsigned_to_nat(0);
    v___x_827_ = l_Std_IterM_toExtTreeSet___auto__1___closed__14;
    v___x_828_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_828_, 0, v___x_827_);
    leanh::lean_ctor_set(v___x_828_, 1, v___x_826_);
    leanh::lean_ctor_set(v___x_828_, 2, v___x_825_);
    return v___x_828_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = leanh::lean_box(0);
    v___x_832_ = l_Std_IterM_toExtTreeSet___auto__1___closed__17;
    v___x_833_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__16_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__16,
    );
    v___x_834_ = leanh::lean_box(2);
    v___x_835_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_835_, 0, v___x_834_);
    leanh::lean_ctor_set(v___x_835_, 1, v___x_833_);
    leanh::lean_ctor_set(v___x_835_, 2, v___x_832_);
    leanh::lean_ctor_set(v___x_835_, 3, v___x_831_);
    return v___x_835_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__18_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__18,
    );
    v___x_837_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__13_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__13,
    );
    v___x_838_ = lean_array_push(v___x_837_, v___x_836_);
    return v___x_838_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_839_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__19_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__19,
    );
    v___x_840_ = l_Std_IterM_toExtTreeSet___auto__1___closed__11;
    v___x_841_ = leanh::lean_box(2);
    v___x_842_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_842_, 0, v___x_841_);
    leanh::lean_ctor_set(v___x_842_, 1, v___x_840_);
    leanh::lean_ctor_set(v___x_842_, 2, v___x_839_);
    return v___x_842_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__20_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__20,
    );
    v___x_844_ = l_Std_IterM_toExtTreeSet___auto__1___closed__5;
    v___x_845_ = lean_array_push(v___x_844_, v___x_843_);
    return v___x_845_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__21_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__21,
    );
    v___x_847_ = l_Std_IterM_toExtTreeSet___auto__1___closed__9;
    v___x_848_ = leanh::lean_box(2);
    v___x_849_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_849_, 0, v___x_848_);
    leanh::lean_ctor_set(v___x_849_, 1, v___x_847_);
    leanh::lean_ctor_set(v___x_849_, 2, v___x_846_);
    return v___x_849_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__22_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__22,
    );
    v___x_851_ = l_Std_IterM_toExtTreeSet___auto__1___closed__5;
    v___x_852_ = lean_array_push(v___x_851_, v___x_850_);
    return v___x_852_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__23_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__23,
    );
    v___x_854_ = l_Std_IterM_toExtTreeSet___auto__1___closed__7;
    v___x_855_ = leanh::lean_box(2);
    v___x_856_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_856_, 0, v___x_855_);
    leanh::lean_ctor_set(v___x_856_, 1, v___x_854_);
    leanh::lean_ctor_set(v___x_856_, 2, v___x_853_);
    return v___x_856_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__24_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__24,
    );
    v___x_858_ = l_Std_IterM_toExtTreeSet___auto__1___closed__5;
    v___x_859_ = lean_array_push(v___x_858_, v___x_857_);
    return v___x_859_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__25_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__25,
    );
    v___x_861_ = l_Std_IterM_toExtTreeSet___auto__1___closed__4;
    v___x_862_ = leanh::lean_box(2);
    v___x_863_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_863_, 0, v___x_862_);
    leanh::lean_ctor_set(v___x_863_, 1, v___x_861_);
    leanh::lean_ctor_set(v___x_863_, 2, v___x_860_);
    return v___x_863_;
}
pub unsafe fn _init_l_Std_IterM_toExtTreeSet___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_864_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__26_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__26,
    );
    return v___x_864_;
}
pub unsafe fn l_Std_IterM_toExtTreeSet___redArg___lam__2(
    mut v_toPure_865_: *mut leanh::LeanObject,
    mut v_toBind_866_: *mut leanh::LeanObject,
    mut v___f_867_: *mut leanh::LeanObject,
    mut v_cmp_868_: *mut leanh::LeanObject,
    mut v_x1_869_: *mut leanh::LeanObject,
    mut v_x2_870_: *mut leanh::LeanObject,
    mut v_x3_871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: u8 = 0;
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_x3_871_);
                leanh::lean_inc(v_x1_869_);
                leanh::lean_inc_ref(v_cmp_868_);
                v___x_877_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(
                    v_cmp_868_, v_x1_869_, v_x3_871_,
                );
                if v___x_877_ == 0 {
                    v___x_878_ = leanh::lean_box(0);
                    v___x_879_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                        v_cmp_868_, v_x1_869_, v___x_878_, v_x3_871_,
                    );
                    v___y_873_ = v___x_879_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_x1_869_);
                    leanh::lean_dec_ref(v_cmp_868_);
                    v___y_873_ = v_x3_871_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_874_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_874_, 0, v___y_873_);
                v___x_875_ = leanh::lean_apply_2(
                    v_toPure_865_,
                    leanh::lean_box(0),
                    v___x_874_,
                );
                v___x_876_ = leanh::lean_apply_4(
                    v_toBind_866_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_875_,
                    v___f_867_,
                );
                return v___x_876_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterM_toExtTreeSet___redArg(
    mut v_inst_880_: *mut leanh::LeanObject,
    mut v_inst_881_: *mut leanh::LeanObject,
    mut v_it_882_: *mut leanh::LeanObject,
    mut v_cmp_883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_884_ = leanh::lean_ctor_get(v_inst_880_, 0);
    leanh::lean_inc_ref(v_toApplicative_884_);
    v_toBind_885_ = leanh::lean_ctor_get(v_inst_880_, 1);
    leanh::lean_inc_n(v_toBind_885_, 2);
    leanh::lean_dec_ref(v_inst_880_);
    v_toPure_886_ = leanh::lean_ctor_get(v_toApplicative_884_, 1);
    leanh::lean_inc_n(v_toPure_886_, 2);
    leanh::lean_dec_ref(v_toApplicative_884_);
    v___x_887_ = leanh::lean_box(1);
    v___f_888_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_888_, 0, v_toBind_885_);
    v___f_889_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_889_, 0, v_toPure_886_);
    v___f_890_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtTreeSet___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_890_, 0, v_toPure_886_);
    leanh::lean_closure_set(v___f_890_, 1, v_toBind_885_);
    leanh::lean_closure_set(v___f_890_, 2, v___f_889_);
    leanh::lean_closure_set(v___f_890_, 3, v_cmp_883_);
    v___x_891_ = leanh::lean_apply_6(
        v_inst_881_,
        v___f_888_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_882_,
        v___x_887_,
        v___f_890_,
    );
    return v___x_891_;
}
pub unsafe fn l_Std_IterM_toExtTreeSet(
    mut v_00_u03b1_892_: *mut leanh::LeanObject,
    mut v_00_u03b2_893_: *mut leanh::LeanObject,
    mut v_m_894_: *mut leanh::LeanObject,
    mut v_inst_895_: *mut leanh::LeanObject,
    mut v_inst_896_: *mut leanh::LeanObject,
    mut v_inst_897_: *mut leanh::LeanObject,
    mut v_it_898_: *mut leanh::LeanObject,
    mut v_cmp_899_: *mut leanh::LeanObject,
    mut v_inst_900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_901_ = leanh::lean_ctor_get(v_inst_895_, 0);
    leanh::lean_inc_ref(v_toApplicative_901_);
    v_toBind_902_ = leanh::lean_ctor_get(v_inst_895_, 1);
    leanh::lean_inc_n(v_toBind_902_, 2);
    leanh::lean_dec_ref(v_inst_895_);
    v_toPure_903_ = leanh::lean_ctor_get(v_toApplicative_901_, 1);
    leanh::lean_inc_n(v_toPure_903_, 2);
    leanh::lean_dec_ref(v_toApplicative_901_);
    v___x_904_ = leanh::lean_box(1);
    v___f_905_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_905_, 0, v_toBind_902_);
    v___f_906_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_906_, 0, v_toPure_903_);
    v___f_907_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtTreeSet___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_907_, 0, v_toPure_903_);
    leanh::lean_closure_set(v___f_907_, 1, v_toBind_902_);
    leanh::lean_closure_set(v___f_907_, 2, v___f_906_);
    leanh::lean_closure_set(v___f_907_, 3, v_cmp_899_);
    v___x_908_ = leanh::lean_apply_6(
        v_inst_897_,
        v___f_905_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_898_,
        v___x_904_,
        v___f_907_,
    );
    return v___x_908_;
}
pub unsafe fn l_Std_IterM_toExtTreeSet___boxed(
    mut v_00_u03b1_909_: *mut leanh::LeanObject,
    mut v_00_u03b2_910_: *mut leanh::LeanObject,
    mut v_m_911_: *mut leanh::LeanObject,
    mut v_inst_912_: *mut leanh::LeanObject,
    mut v_inst_913_: *mut leanh::LeanObject,
    mut v_inst_914_: *mut leanh::LeanObject,
    mut v_it_915_: *mut leanh::LeanObject,
    mut v_cmp_916_: *mut leanh::LeanObject,
    mut v_inst_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_918_ = l_Std_IterM_toExtTreeSet(
        v_00_u03b1_909_,
        v_00_u03b2_910_,
        v_m_911_,
        v_inst_912_,
        v_inst_913_,
        v_inst_914_,
        v_it_915_,
        v_cmp_916_,
        v_inst_917_,
    );
    leanh::lean_dec(v_inst_913_);
    return v_res_918_;
}
pub unsafe fn _init_l_Std_IterM_Total_toExtTreeSet___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_919_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_IterM_toExtTreeSet___auto__1___closed__26_once),
        _init_l_Std_IterM_toExtTreeSet___auto__1___closed__26,
    );
    return v___x_919_;
}
pub unsafe fn l_Std_IterM_Total_toExtTreeSet___redArg(
    mut v_inst_920_: *mut leanh::LeanObject,
    mut v_inst_921_: *mut leanh::LeanObject,
    mut v_it_922_: *mut leanh::LeanObject,
    mut v_cmp_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_924_ = leanh::lean_ctor_get(v_inst_920_, 0);
    leanh::lean_inc_ref(v_toApplicative_924_);
    v_toBind_925_ = leanh::lean_ctor_get(v_inst_920_, 1);
    leanh::lean_inc_n(v_toBind_925_, 2);
    leanh::lean_dec_ref(v_inst_920_);
    v_toPure_926_ = leanh::lean_ctor_get(v_toApplicative_924_, 1);
    leanh::lean_inc_n(v_toPure_926_, 2);
    leanh::lean_dec_ref(v_toApplicative_924_);
    v___x_927_ = leanh::lean_box(1);
    v___f_928_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_928_, 0, v_toBind_925_);
    v___f_929_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_929_, 0, v_toPure_926_);
    v___f_930_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtTreeSet___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_930_, 0, v_toPure_926_);
    leanh::lean_closure_set(v___f_930_, 1, v_toBind_925_);
    leanh::lean_closure_set(v___f_930_, 2, v___f_929_);
    leanh::lean_closure_set(v___f_930_, 3, v_cmp_923_);
    v___x_931_ = leanh::lean_apply_6(
        v_inst_921_,
        v___f_928_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_922_,
        v___x_927_,
        v___f_930_,
    );
    return v___x_931_;
}
pub unsafe fn l_Std_IterM_Total_toExtTreeSet(
    mut v_00_u03b1_932_: *mut leanh::LeanObject,
    mut v_00_u03b2_933_: *mut leanh::LeanObject,
    mut v_m_934_: *mut leanh::LeanObject,
    mut v_inst_935_: *mut leanh::LeanObject,
    mut v_inst_936_: *mut leanh::LeanObject,
    mut v_inst_937_: *mut leanh::LeanObject,
    mut v_inst_938_: *mut leanh::LeanObject,
    mut v_it_939_: *mut leanh::LeanObject,
    mut v_cmp_940_: *mut leanh::LeanObject,
    mut v_inst_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_942_ = leanh::lean_ctor_get(v_inst_935_, 0);
    leanh::lean_inc_ref(v_toApplicative_942_);
    v_toBind_943_ = leanh::lean_ctor_get(v_inst_935_, 1);
    leanh::lean_inc_n(v_toBind_943_, 2);
    leanh::lean_dec_ref(v_inst_935_);
    v_toPure_944_ = leanh::lean_ctor_get(v_toApplicative_942_, 1);
    leanh::lean_inc_n(v_toPure_944_, 2);
    leanh::lean_dec_ref(v_toApplicative_942_);
    v___x_945_ = leanh::lean_box(1);
    v___f_946_ = leanh::lean_alloc_closure(
        l_Std_IterM_toHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_946_, 0, v_toBind_943_);
    v___f_947_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_947_, 0, v_toPure_944_);
    v___f_948_ = leanh::lean_alloc_closure(
        l_Std_IterM_toExtTreeSet___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_948_, 0, v_toPure_944_);
    leanh::lean_closure_set(v___f_948_, 1, v_toBind_943_);
    leanh::lean_closure_set(v___f_948_, 2, v___f_947_);
    leanh::lean_closure_set(v___f_948_, 3, v_cmp_940_);
    v___x_949_ = leanh::lean_apply_6(
        v_inst_938_,
        v___f_946_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_it_939_,
        v___x_945_,
        v___f_948_,
    );
    return v___x_949_;
}
pub unsafe fn l_Std_IterM_Total_toExtTreeSet___boxed(
    mut v_00_u03b1_950_: *mut leanh::LeanObject,
    mut v_00_u03b2_951_: *mut leanh::LeanObject,
    mut v_m_952_: *mut leanh::LeanObject,
    mut v_inst_953_: *mut leanh::LeanObject,
    mut v_inst_954_: *mut leanh::LeanObject,
    mut v_inst_955_: *mut leanh::LeanObject,
    mut v_inst_956_: *mut leanh::LeanObject,
    mut v_it_957_: *mut leanh::LeanObject,
    mut v_cmp_958_: *mut leanh::LeanObject,
    mut v_inst_959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Std_IterM_Total_toExtTreeSet(
        v_00_u03b1_950_,
        v_00_u03b2_951_,
        v_m_952_,
        v_inst_953_,
        v_inst_954_,
        v_inst_955_,
        v_inst_956_,
        v_it_957_,
        v_cmp_958_,
        v_inst_959_,
    );
    leanh::lean_dec(v_inst_954_);
    return v_res_960_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Consumers_Monadic_Set(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtHashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtTreeSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Consumers_Monadic_Set(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_IterM_toExtTreeSet___auto__1 = _init_l_Std_IterM_toExtTreeSet___auto__1();
    leanh::lean_mark_persistent(l_Std_IterM_toExtTreeSet___auto__1);
    l_Std_IterM_Total_toExtTreeSet___auto__1 = _init_l_Std_IterM_Total_toExtTreeSet___auto__1();
    leanh::lean_mark_persistent(l_Std_IterM_Total_toExtTreeSet___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Consumers_Monadic_Set(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_ExtHashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_ExtTreeSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Consumers_Monadic_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Consumers_Monadic_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Consumers_Monadic_Set(builtin);
}
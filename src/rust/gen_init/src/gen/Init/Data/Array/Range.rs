// Lean compiler output
// Module: Init.Data.Array.Range
// Imports: Init.Data.Array.Basic Init.Data.Array.OfFn Init.BinderPredicates Init.Data.Nat.Lemmas Init.Ext Init.ByCases Init.Data.Array.Count Init.Data.Array.MapIdx Init.Data.Array.Zip Init.Data.List.Find Init.Data.List.Nat.Range Init.Data.List.Range
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Count::{
    initialize_Init_Data_Array_Count, runtime_initialize_Init_Data_Array_Count,
};
use crate::r#gen::Init::Data::Array::MapIdx::{
    initialize_Init_Data_Array_MapIdx, runtime_initialize_Init_Data_Array_MapIdx,
};
use crate::r#gen::Init::Data::Array::OfFn::{
    initialize_Init_Data_Array_OfFn, runtime_initialize_Init_Data_Array_OfFn,
};
use crate::r#gen::Init::Data::Array::Zip::{
    initialize_Init_Data_Array_Zip, runtime_initialize_Init_Data_Array_Zip,
};
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::List::Nat::Range::{
    initialize_Init_Data_List_Nat_Range, runtime_initialize_Init_Data_List_Nat_Range,
};
use crate::r#gen::Init::Data::List::Range::{
    initialize_Init_Data_List_Range, runtime_initialize_Init_Data_List_Range,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::ffi::{lean_array_push, lean_nat_dec_eq, lean_nat_sub};
pub static l_Array_count__range_x27___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Array_count__range_x27___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_count__range_x27___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Array_count__range_x27___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_count__range_x27___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Array_count__range_x27___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_count__range_x27___auto__1___closed__3_value: crate::leanh::LeanStringObject<
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
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Array_count__range_x27___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Array_count__range_x27___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_count__range_x27___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_count__range_x27___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_count__range_x27___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_count__range_x27___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_count__range_x27___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Array_count__range_x27___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_count__range_x27___auto__1___closed__6_value: crate::leanh::LeanStringObject<
    19,
> = crate::leanh::LeanStringObject {
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
static mut l_Array_count__range_x27___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Array_count__range_x27___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_count__range_x27___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Array_count__range_x27___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_count__range_x27___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_count__range_x27___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_count__range_x27___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Array_count__range_x27___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_count__range_x27___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_count__range_x27___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_count__range_x27___auto__1___closed__10_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 105, 109, 112, 0],
};
static mut l_Array_count__range_x27___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Array_count__range_x27___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Array_count__range_x27___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Array_count__range_x27___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Array_count__range_x27___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            12783917532758215986 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_count__range_x27___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_count__range_x27___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_count__range_x27___auto__1___closed__14_value: crate::leanh::LeanStringObject<
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Array_count__range_x27___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Array_count__range_x27___auto__1___closed__15_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Array_count__range_x27___auto__1___closed__15_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__15_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Array_count__range_x27___auto__1___closed__15_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__15_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Array_count__range_x27___auto__1___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__15_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            3488656302031949961 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_count__range_x27___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_count__range_x27___auto__1___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_count__range_x27___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_count__range_x27___auto__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_count__range_x27___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_count__range_x27___auto__1___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_count__range_x27___auto__1___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Array_count__range_x27___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___redArg(
    mut v_x_122_: *mut crate::leanh::LeanObject,
    mut v_h__1_123_: *mut crate::leanh::LeanObject,
    mut v_h__2_124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_126_: u8 = 0;
    v_zero_125_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_126_ = lean_nat_dec_eq(v_x_122_, v_zero_125_);
    if v_isZero_126_ == 1 {
        let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_123_);
        v___x_127_ = crate::leanh::lean_apply_1(v_h__2_124_, crate::leanh::lean_box(0));
        return v___x_127_;
    } else {
        let mut v_one_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_124_);
        v_one_128_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_129_ = lean_nat_sub(v_x_122_, v_one_128_);
        v___x_130_ = crate::leanh::lean_apply_2(v_h__1_123_, v_n_129_, crate::leanh::lean_box(0));
        return v___x_130_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___redArg___boxed(
    mut v_x_131_: *mut crate::leanh::LeanObject,
    mut v_h__1_132_: *mut crate::leanh::LeanObject,
    mut v_h__2_133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_134_ = l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___redArg(
        v_x_131_,
        v_h__1_132_,
        v_h__2_133_,
    );
    crate::leanh::lean_dec(v_x_131_);
    return v_res_134_;
}
pub unsafe fn l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter(
    mut v_n_135_: *mut crate::leanh::LeanObject,
    mut v_motive_136_: *mut crate::leanh::LeanObject,
    mut v_x_137_: *mut crate::leanh::LeanObject,
    mut v_x_138_: *mut crate::leanh::LeanObject,
    mut v_h__1_139_: *mut crate::leanh::LeanObject,
    mut v_h__2_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_142_: u8 = 0;
    v_zero_141_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_142_ = lean_nat_dec_eq(v_x_137_, v_zero_141_);
    if v_isZero_142_ == 1 {
        let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_139_);
        v___x_143_ = crate::leanh::lean_apply_1(v_h__2_140_, crate::leanh::lean_box(0));
        return v___x_143_;
    } else {
        let mut v_one_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_140_);
        v_one_144_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_145_ = lean_nat_sub(v_x_137_, v_one_144_);
        v___x_146_ = crate::leanh::lean_apply_2(v_h__1_139_, v_n_145_, crate::leanh::lean_box(0));
        return v___x_146_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___boxed(
    mut v_n_147_: *mut crate::leanh::LeanObject,
    mut v_motive_148_: *mut crate::leanh::LeanObject,
    mut v_x_149_: *mut crate::leanh::LeanObject,
    mut v_x_150_: *mut crate::leanh::LeanObject,
    mut v_h__1_151_: *mut crate::leanh::LeanObject,
    mut v_h__2_152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_153_ = l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter(
        v_n_147_,
        v_motive_148_,
        v_x_149_,
        v_x_150_,
        v_h__1_151_,
        v_h__2_152_,
    );
    crate::leanh::lean_dec(v_x_149_);
    crate::leanh::lean_dec(v_n_147_);
    return v_res_153_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_180_ = l_Array_count__range_x27___auto__1___closed__10;
    v___x_181_ = l_Lean_mkAtom(v___x_180_);
    return v___x_181_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__12_once),
        _init_l_Array_count__range_x27___auto__1___closed__12,
    );
    v___x_183_ = l_Array_count__range_x27___auto__1___closed__5;
    v___x_184_ = lean_array_push(v___x_183_, v___x_182_);
    return v___x_184_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_195_ = l_Array_count__range_x27___auto__1___closed__16;
    v___x_196_ = l_Array_count__range_x27___auto__1___closed__5;
    v___x_197_ = lean_array_push(v___x_196_, v___x_195_);
    return v___x_197_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_198_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__17_once),
        _init_l_Array_count__range_x27___auto__1___closed__17,
    );
    v___x_199_ = l_Array_count__range_x27___auto__1___closed__15;
    v___x_200_ = crate::leanh::lean_box(2);
    v___x_201_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_201_, 0, v___x_200_);
    crate::leanh::lean_ctor_set(v___x_201_, 1, v___x_199_);
    crate::leanh::lean_ctor_set(v___x_201_, 2, v___x_198_);
    return v___x_201_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_202_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__18_once),
        _init_l_Array_count__range_x27___auto__1___closed__18,
    );
    v___x_203_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__13_once),
        _init_l_Array_count__range_x27___auto__1___closed__13,
    );
    v___x_204_ = lean_array_push(v___x_203_, v___x_202_);
    return v___x_204_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_205_ = l_Array_count__range_x27___auto__1___closed__16;
    v___x_206_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__19_once),
        _init_l_Array_count__range_x27___auto__1___closed__19,
    );
    v___x_207_ = lean_array_push(v___x_206_, v___x_205_);
    return v___x_207_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_208_ = l_Array_count__range_x27___auto__1___closed__16;
    v___x_209_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__20_once),
        _init_l_Array_count__range_x27___auto__1___closed__20,
    );
    v___x_210_ = lean_array_push(v___x_209_, v___x_208_);
    return v___x_210_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_211_ = l_Array_count__range_x27___auto__1___closed__16;
    v___x_212_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__21_once),
        _init_l_Array_count__range_x27___auto__1___closed__21,
    );
    v___x_213_ = lean_array_push(v___x_212_, v___x_211_);
    return v___x_213_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_214_ = l_Array_count__range_x27___auto__1___closed__16;
    v___x_215_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__22_once),
        _init_l_Array_count__range_x27___auto__1___closed__22,
    );
    v___x_216_ = lean_array_push(v___x_215_, v___x_214_);
    return v___x_216_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_217_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__23_once),
        _init_l_Array_count__range_x27___auto__1___closed__23,
    );
    v___x_218_ = l_Array_count__range_x27___auto__1___closed__11;
    v___x_219_ = crate::leanh::lean_box(2);
    v___x_220_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_220_, 0, v___x_219_);
    crate::leanh::lean_ctor_set(v___x_220_, 1, v___x_218_);
    crate::leanh::lean_ctor_set(v___x_220_, 2, v___x_217_);
    return v___x_220_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_221_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__24_once),
        _init_l_Array_count__range_x27___auto__1___closed__24,
    );
    v___x_222_ = l_Array_count__range_x27___auto__1___closed__5;
    v___x_223_ = lean_array_push(v___x_222_, v___x_221_);
    return v___x_223_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_224_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__25_once),
        _init_l_Array_count__range_x27___auto__1___closed__25,
    );
    v___x_225_ = l_Array_count__range_x27___auto__1___closed__9;
    v___x_226_ = crate::leanh::lean_box(2);
    v___x_227_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_227_, 0, v___x_226_);
    crate::leanh::lean_ctor_set(v___x_227_, 1, v___x_225_);
    crate::leanh::lean_ctor_set(v___x_227_, 2, v___x_224_);
    return v___x_227_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_228_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__26_once),
        _init_l_Array_count__range_x27___auto__1___closed__26,
    );
    v___x_229_ = l_Array_count__range_x27___auto__1___closed__5;
    v___x_230_ = lean_array_push(v___x_229_, v___x_228_);
    return v___x_230_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_231_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__27_once),
        _init_l_Array_count__range_x27___auto__1___closed__27,
    );
    v___x_232_ = l_Array_count__range_x27___auto__1___closed__7;
    v___x_233_ = crate::leanh::lean_box(2);
    v___x_234_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_234_, 0, v___x_233_);
    crate::leanh::lean_ctor_set(v___x_234_, 1, v___x_232_);
    crate::leanh::lean_ctor_set(v___x_234_, 2, v___x_231_);
    return v___x_234_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_235_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__28_once),
        _init_l_Array_count__range_x27___auto__1___closed__28,
    );
    v___x_236_ = l_Array_count__range_x27___auto__1___closed__5;
    v___x_237_ = lean_array_push(v___x_236_, v___x_235_);
    return v___x_237_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_238_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__29_once),
        _init_l_Array_count__range_x27___auto__1___closed__29,
    );
    v___x_239_ = l_Array_count__range_x27___auto__1___closed__4;
    v___x_240_ = crate::leanh::lean_box(2);
    v___x_241_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_241_, 0, v___x_240_);
    crate::leanh::lean_ctor_set(v___x_241_, 1, v___x_239_);
    crate::leanh::lean_ctor_set(v___x_241_, 2, v___x_238_);
    return v___x_241_;
}
pub unsafe fn _init_l_Array_count__range_x27___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_242_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Array_count__range_x27___auto__1___closed__30_once),
        _init_l_Array_count__range_x27___auto__1___closed__30,
    );
    return v___x_242_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Range(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Range(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Array_count__range_x27___auto__1 = _init_l_Array_count__range_x27___auto__1();
    crate::leanh::lean_mark_persistent(l_Array_count__range_x27___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Range(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Range(builtin);
}

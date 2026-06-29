// Lean compiler output
// Module: Lean.Meta.NatTable
// Imports: Lean.Meta.Basic Lean.Meta.InferType Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_eq,
    lean_nat_shiftr, lean_nat_sub, lean_panic_fn_borrowed,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkRawNatLit};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::InferType::{
    initialize_Lean_Meta_InferType, l_Lean_Meta_getLevel, runtime_initialize_Lean_Meta_InferType,
};
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value:
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
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value:
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
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value:
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
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3_value:
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
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_value:
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
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6_value:
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
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8_value:
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
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10_value:
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
    m_data: [111, 109, 101, 103, 97, 0],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_2:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        14893461734720614794 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_2:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__0_value:
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
    m_data: [99, 111, 110, 100, 0],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        105488867511536770 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__2_value:
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
    m_data: [78, 97, 116, 0],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__3_value:
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
    m_data: [98, 108, 101, 0],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        2386391158190226450 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00mkNatLookupTable_spec__0___closed__0_value:
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
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00mkNatLookupTable_spec__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00mkNatLookupTable_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_mkNatLookupTable___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 78, 97, 116, 84, 97, 98, 108, 101, 0,
        ],
    };
static mut l_mkNatLookupTable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkNatLookupTable___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_mkNatLookupTable___closed__1_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            109, 107, 78, 97, 116, 76, 111, 111, 107, 117, 112, 84, 97, 98, 108, 101, 0,
        ],
    };
static mut l_mkNatLookupTable___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkNatLookupTable___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_mkNatLookupTable___closed__2_value: crate::leanh::LeanStringObject<43> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 43,
        m_capacity: 43,
        m_length: 42,
        m_data: [
            109, 107, 78, 97, 116, 76, 111, 111, 107, 117, 112, 84, 97, 98, 108, 101, 58, 32, 101,
            120, 112, 101, 99, 116, 101, 100, 32, 110, 111, 110, 45, 101, 109, 112, 116, 121, 32,
            97, 114, 114, 97, 121, 0,
        ],
    };
static mut l_mkNatLookupTable___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkNatLookupTable___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_mkNatLookupTable___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkNatLookupTable___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_245_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10;
    v___x_246_ = l_Lean_mkAtom(v___x_245_);
    return v___x_246_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12,
    );
    v___x_248_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5;
    v___x_249_ = lean_array_push(v___x_248_, v___x_247_);
    return v___x_249_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_260_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16;
    v___x_261_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5;
    v___x_262_ = lean_array_push(v___x_261_, v___x_260_);
    return v___x_262_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_263_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17,
    );
    v___x_264_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15;
    v___x_265_ = crate::leanh::lean_box(2);
    v___x_266_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_266_, 0, v___x_265_);
    crate::leanh::lean_ctor_set(v___x_266_, 1, v___x_264_);
    crate::leanh::lean_ctor_set(v___x_266_, 2, v___x_263_);
    return v___x_266_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_267_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18,
    );
    v___x_268_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13,
    );
    v___x_269_ = lean_array_push(v___x_268_, v___x_267_);
    return v___x_269_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19,
    );
    v___x_271_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11;
    v___x_272_ = crate::leanh::lean_box(2);
    v___x_273_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_273_, 0, v___x_272_);
    crate::leanh::lean_ctor_set(v___x_273_, 1, v___x_271_);
    crate::leanh::lean_ctor_set(v___x_273_, 2, v___x_270_);
    return v___x_273_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_274_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20,
    );
    v___x_275_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5;
    v___x_276_ = lean_array_push(v___x_275_, v___x_274_);
    return v___x_276_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_277_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21,
    );
    v___x_278_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9;
    v___x_279_ = crate::leanh::lean_box(2);
    v___x_280_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_280_, 0, v___x_279_);
    crate::leanh::lean_ctor_set(v___x_280_, 1, v___x_278_);
    crate::leanh::lean_ctor_set(v___x_280_, 2, v___x_277_);
    return v___x_280_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_281_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22,
    );
    v___x_282_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5;
    v___x_283_ = lean_array_push(v___x_282_, v___x_281_);
    return v___x_283_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_284_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23,
    );
    v___x_285_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7;
    v___x_286_ = crate::leanh::lean_box(2);
    v___x_287_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_287_, 0, v___x_286_);
    crate::leanh::lean_ctor_set(v___x_287_, 1, v___x_285_);
    crate::leanh::lean_ctor_set(v___x_287_, 2, v___x_284_);
    return v___x_287_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_288_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24,
    );
    v___x_289_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5;
    v___x_290_ = lean_array_push(v___x_289_, v___x_288_);
    return v___x_290_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25,
    );
    v___x_292_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4;
    v___x_293_ = crate::leanh::lean_box(2);
    v___x_294_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_294_, 0, v___x_293_);
    crate::leanh::lean_ctor_set(v___x_294_, 1, v___x_292_);
    crate::leanh::lean_ctor_set(v___x_294_, 2, v___x_291_);
    return v___x_294_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26,
    );
    return v___x_295_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_296_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26_once
        ),
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26,
    );
    return v___x_296_;
}
pub unsafe fn _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_305_ = crate::leanh::lean_box(0);
    v___x_306_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4;
    v___x_307_ = l_Lean_mkConst(v___x_306_, v___x_305_);
    return v___x_307_;
}
pub unsafe fn l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(
    mut v_i_308_: *mut crate::leanh::LeanObject,
    mut v_type_309_: *mut crate::leanh::LeanObject,
    mut v_es_310_: *mut crate::leanh::LeanObject,
    mut v_u_311_: *mut crate::leanh::LeanObject,
    mut v_start_312_: *mut crate::leanh::LeanObject,
    mut v_stop_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: u8 = 0;
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_326_: u8 = 0;
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_339_: u8 = 0;
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_315_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_316_ = lean_nat_add(v_start_312_, v___x_315_);
                v___x_317_ = lean_nat_dec_eq(v___x_316_, v_stop_313_);
                crate::leanh::lean_dec(v___x_316_);
                if v___x_317_ == 0 {
                    v___x_318_ = lean_nat_add(v_start_312_, v_stop_313_);
                    v_mid_319_ = lean_nat_shiftr(v___x_318_, v___x_315_);
                    crate::leanh::lean_dec(v___x_318_);
                    crate::leanh::lean_inc_n(v_u_311_, 2);
                    crate::leanh::lean_inc_ref_n(v_type_309_, 2);
                    crate::leanh::lean_inc_ref_n(v_i_308_, 2);
                    v___x_320_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(
                        v_i_308_,
                        v_type_309_,
                        v_es_310_,
                        v_u_311_,
                        v_start_312_,
                        v_mid_319_,
                    );
                    v_a_321_ = crate::leanh::lean_ctor_get(v___x_320_, 0);
                    crate::leanh::lean_inc(v_a_321_);
                    crate::leanh::lean_dec_ref(v___x_320_);
                    v___x_322_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(
                        v_i_308_,
                        v_type_309_,
                        v_es_310_,
                        v_u_311_,
                        v_mid_319_,
                        v_stop_313_,
                    );
                    v_a_323_ = crate::leanh::lean_ctor_get(v___x_322_, 0);
                    v_isSharedCheck_339_ = (!crate::leanh::lean_is_exclusive(v___x_322_)) as u8;
                    if v_isSharedCheck_339_ == 0 {
                        v___x_325_ = v___x_322_;
                        v_isShared_326_ = v_isSharedCheck_339_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_323_);
                        crate::leanh::lean_dec(v___x_322_);
                        v___x_325_ = crate::leanh::lean_box(0);
                        v_isShared_326_ = v_isSharedCheck_339_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_u_311_);
                    crate::leanh::lean_dec_ref(v_type_309_);
                    crate::leanh::lean_dec_ref(v_i_308_);
                    v___x_340_ = lean_array_fget_borrowed(v_es_310_, v_start_312_);
                    crate::leanh::lean_inc(v___x_340_);
                    v___x_341_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_341_, 0, v___x_340_);
                    return v___x_341_;
                }
            }
            1 => {
                v___x_327_ =
                    l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__1;
                v___x_328_ = crate::leanh::lean_box(0);
                v___x_329_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_329_, 0, v_u_311_);
                crate::leanh::lean_ctor_set(v___x_329_, 1, v___x_328_);
                v___x_330_ = l_Lean_mkConst(v___x_327_, v___x_329_);
                v___x_331_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5_once), _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5);
                v___x_332_ = lean_nat_sub(v_mid_319_, v___x_315_);
                crate::leanh::lean_dec(v_mid_319_);
                v___x_333_ = l_Lean_mkRawNatLit(v___x_332_);
                v___x_334_ = l_Lean_mkAppB(v___x_331_, v_i_308_, v___x_333_);
                v___x_335_ = l_Lean_mkApp4(v___x_330_, v_type_309_, v___x_334_, v_a_321_, v_a_323_);
                if v_isShared_326_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_325_, 0, v___x_335_);
                    v___x_337_ = v___x_325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_338_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
                    v___x_337_ = v_reuseFailAlloc_338_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_337_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___boxed(
    mut v_i_342_: *mut crate::leanh::LeanObject,
    mut v_type_343_: *mut crate::leanh::LeanObject,
    mut v_es_344_: *mut crate::leanh::LeanObject,
    mut v_u_345_: *mut crate::leanh::LeanObject,
    mut v_start_346_: *mut crate::leanh::LeanObject,
    mut v_stop_347_: *mut crate::leanh::LeanObject,
    mut v_a_348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_349_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(
        v_i_342_,
        v_type_343_,
        v_es_344_,
        v_u_345_,
        v_start_346_,
        v_stop_347_,
    );
    crate::leanh::lean_dec(v_stop_347_);
    crate::leanh::lean_dec(v_start_346_);
    crate::leanh::lean_dec_ref(v_es_344_);
    return v_res_349_;
}
pub unsafe fn l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go(
    mut v_i_350_: *mut crate::leanh::LeanObject,
    mut v_type_351_: *mut crate::leanh::LeanObject,
    mut v_es_352_: *mut crate::leanh::LeanObject,
    mut v_u_353_: *mut crate::leanh::LeanObject,
    mut v_start_354_: *mut crate::leanh::LeanObject,
    mut v_stop_355_: *mut crate::leanh::LeanObject,
    mut v_hstart_356_: *mut crate::leanh::LeanObject,
    mut v_hstop_357_: *mut crate::leanh::LeanObject,
    mut v_a_358_: *mut crate::leanh::LeanObject,
    mut v_a_359_: *mut crate::leanh::LeanObject,
    mut v_a_360_: *mut crate::leanh::LeanObject,
    mut v_a_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_363_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(
        v_i_350_,
        v_type_351_,
        v_es_352_,
        v_u_353_,
        v_start_354_,
        v_stop_355_,
    );
    return v___x_363_;
}
pub unsafe fn l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___boxed(
    mut v_i_364_: *mut crate::leanh::LeanObject,
    mut v_type_365_: *mut crate::leanh::LeanObject,
    mut v_es_366_: *mut crate::leanh::LeanObject,
    mut v_u_367_: *mut crate::leanh::LeanObject,
    mut v_start_368_: *mut crate::leanh::LeanObject,
    mut v_stop_369_: *mut crate::leanh::LeanObject,
    mut v_hstart_370_: *mut crate::leanh::LeanObject,
    mut v_hstop_371_: *mut crate::leanh::LeanObject,
    mut v_a_372_: *mut crate::leanh::LeanObject,
    mut v_a_373_: *mut crate::leanh::LeanObject,
    mut v_a_374_: *mut crate::leanh::LeanObject,
    mut v_a_375_: *mut crate::leanh::LeanObject,
    mut v_a_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_377_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go(
        v_i_364_,
        v_type_365_,
        v_es_366_,
        v_u_367_,
        v_start_368_,
        v_stop_369_,
        v_hstart_370_,
        v_hstop_371_,
        v_a_372_,
        v_a_373_,
        v_a_374_,
        v_a_375_,
    );
    crate::leanh::lean_dec(v_a_375_);
    crate::leanh::lean_dec_ref(v_a_374_);
    crate::leanh::lean_dec(v_a_373_);
    crate::leanh::lean_dec_ref(v_a_372_);
    crate::leanh::lean_dec(v_stop_369_);
    crate::leanh::lean_dec(v_start_368_);
    crate::leanh::lean_dec_ref(v_es_366_);
    return v_res_377_;
}
pub unsafe fn l_panic___at___00mkNatLookupTable_spec__0(
    mut v_msg_379_: *mut crate::leanh::LeanObject,
    mut v___y_380_: *mut crate::leanh::LeanObject,
    mut v___y_381_: *mut crate::leanh::LeanObject,
    mut v___y_382_: *mut crate::leanh::LeanObject,
    mut v___y_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133__overap_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_385_ = l_panic___at___00mkNatLookupTable_spec__0___closed__0;
    v___x_133__overap_386_ = lean_panic_fn_borrowed(v___f_385_, v_msg_379_);
    crate::leanh::lean_inc(v___y_383_);
    crate::leanh::lean_inc_ref(v___y_382_);
    crate::leanh::lean_inc(v___y_381_);
    crate::leanh::lean_inc_ref(v___y_380_);
    v___x_387_ = crate::leanh::lean_apply_5(
        v___x_133__overap_386_,
        v___y_380_,
        v___y_381_,
        v___y_382_,
        v___y_383_,
        crate::leanh::lean_box(0),
    );
    return v___x_387_;
}
pub unsafe fn l_panic___at___00mkNatLookupTable_spec__0___boxed(
    mut v_msg_388_: *mut crate::leanh::LeanObject,
    mut v___y_389_: *mut crate::leanh::LeanObject,
    mut v___y_390_: *mut crate::leanh::LeanObject,
    mut v___y_391_: *mut crate::leanh::LeanObject,
    mut v___y_392_: *mut crate::leanh::LeanObject,
    mut v___y_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_394_ = l_panic___at___00mkNatLookupTable_spec__0(
        v_msg_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_,
    );
    crate::leanh::lean_dec(v___y_392_);
    crate::leanh::lean_dec_ref(v___y_391_);
    crate::leanh::lean_dec(v___y_390_);
    crate::leanh::lean_dec_ref(v___y_389_);
    return v_res_394_;
}
pub unsafe fn _init_l_mkNatLookupTable___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = l_mkNatLookupTable___closed__2;
    v___x_399_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_400_ = crate::leanh::lean_unsigned_to_nat(25);
    v___x_401_ = l_mkNatLookupTable___closed__1;
    v___x_402_ = l_mkNatLookupTable___closed__0;
    v___x_403_ =
        l_mkPanicMessageWithDecl(v___x_402_, v___x_401_, v___x_400_, v___x_399_, v___x_398_);
    return v___x_403_;
}
pub unsafe fn l_mkNatLookupTable(
    mut v_i_404_: *mut crate::leanh::LeanObject,
    mut v_type_405_: *mut crate::leanh::LeanObject,
    mut v_es_406_: *mut crate::leanh::LeanObject,
    mut v_a_407_: *mut crate::leanh::LeanObject,
    mut v_a_408_: *mut crate::leanh::LeanObject,
    mut v_a_409_: *mut crate::leanh::LeanObject,
    mut v_a_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: u8 = 0;
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_421_: u8 = 0;
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_425_: u8 = 0;
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_412_ = lean_array_get_size(v_es_406_);
                v___x_413_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_414_ = lean_nat_dec_eq(v___x_412_, v___x_413_);
                if v___x_414_ == 0 {
                    crate::leanh::lean_inc_ref(v_type_405_);
                    v___x_415_ =
                        l_Lean_Meta_getLevel(v_type_405_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
                    if crate::leanh::lean_obj_tag(v___x_415_) == 0 {
                        v_a_416_ = crate::leanh::lean_ctor_get(v___x_415_, 0);
                        crate::leanh::lean_inc(v_a_416_);
                        crate::leanh::lean_dec_ref_known(v___x_415_, 1);
                        v___x_417_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(
                            v_i_404_,
                            v_type_405_,
                            v_es_406_,
                            v_a_416_,
                            v___x_413_,
                            v___x_412_,
                        );
                        return v___x_417_;
                    } else {
                        crate::leanh::lean_dec_ref(v_type_405_);
                        crate::leanh::lean_dec_ref(v_i_404_);
                        v_a_418_ = crate::leanh::lean_ctor_get(v___x_415_, 0);
                        v_isSharedCheck_425_ = (!crate::leanh::lean_is_exclusive(v___x_415_)) as u8;
                        if v_isSharedCheck_425_ == 0 {
                            v___x_420_ = v___x_415_;
                            v_isShared_421_ = v_isSharedCheck_425_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_418_);
                            crate::leanh::lean_dec(v___x_415_);
                            v___x_420_ = crate::leanh::lean_box(0);
                            v_isShared_421_ = v_isSharedCheck_425_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_405_);
                    crate::leanh::lean_dec_ref(v_i_404_);
                    v___x_426_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_mkNatLookupTable___closed__3),
                        core::ptr::addr_of_mut!(l_mkNatLookupTable___closed__3_once),
                        _init_l_mkNatLookupTable___closed__3,
                    );
                    v___x_427_ = l_panic___at___00mkNatLookupTable_spec__0(
                        v___x_426_, v_a_407_, v_a_408_, v_a_409_, v_a_410_,
                    );
                    return v___x_427_;
                }
            }
            1 => {
                if v_isShared_421_ == 0 {
                    v___x_423_ = v___x_420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
                    v___x_423_ = v_reuseFailAlloc_424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkNatLookupTable___boxed(
    mut v_i_428_: *mut crate::leanh::LeanObject,
    mut v_type_429_: *mut crate::leanh::LeanObject,
    mut v_es_430_: *mut crate::leanh::LeanObject,
    mut v_a_431_: *mut crate::leanh::LeanObject,
    mut v_a_432_: *mut crate::leanh::LeanObject,
    mut v_a_433_: *mut crate::leanh::LeanObject,
    mut v_a_434_: *mut crate::leanh::LeanObject,
    mut v_a_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_436_ = l_mkNatLookupTable(
        v_i_428_,
        v_type_429_,
        v_es_430_,
        v_a_431_,
        v_a_432_,
        v_a_433_,
        v_a_434_,
    );
    crate::leanh::lean_dec(v_a_434_);
    crate::leanh::lean_dec_ref(v_a_433_);
    crate::leanh::lean_dec(v_a_432_);
    crate::leanh::lean_dec_ref(v_a_431_);
    crate::leanh::lean_dec_ref(v_es_430_);
    return v_res_436_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_NatTable(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_NatTable(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1 =
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1,
    );
    l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3 =
        _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_NatTable(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatTable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_NatTable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_NatTable(builtin);
}

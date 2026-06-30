// Lean compiler output
// Module: Lean.Elab.ErrorUtils
// Imports: Lean.Message
use crate::ffi::{lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mod, lean_string_append};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Lean::Message::{
    initialize_Lean_Message, l_Lean_MessageData_nil, l_Lean_MessageData_ofFormat,
    l_Lean_stringToMessageData, runtime_initialize_Lean_Message,
};
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [114, 100, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [110, 100, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 101, 110, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [110, 105, 110, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 105, 103, 104, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 101, 118, 101, 110, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 105, 120, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 105, 102, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [102, 111, 117, 114, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 104, 105, 114, 100, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 101, 99, 111, 110, 100, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 105, 114, 115, 116, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [122, 101, 114, 111, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__1_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 97, 110, 100, 32, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__2_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__3_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [44, 32, 97, 110, 100, 32, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__4_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__1_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__3_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__4_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__4_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__4_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__3_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__6_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [115, 0]};
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal(
    mut v_x_189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: u8 = 0;
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: u8 = 0;
    let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: u8 = 0;
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: u8 = 0;
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: u8 = 0;
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: u8 = 0;
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: u8 = 0;
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: u8 = 0;
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: u8 = 0;
    let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: u8 = 0;
    let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_212_: u8 = 0;
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: u8 = 0;
    let mut v___x_215_: u8 = 0;
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: u8 = 0;
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: u8 = 0;
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: u8 = 0;
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_190_ = leanh::lean_unsigned_to_nat(0);
                v___x_191_ = lean_nat_dec_eq(v_x_189_, v___x_190_);
                if v___x_191_ == 0 {
                    v___x_192_ = leanh::lean_unsigned_to_nat(1);
                    v___x_193_ = lean_nat_dec_eq(v_x_189_, v___x_192_);
                    if v___x_193_ == 0 {
                        v___x_194_ = leanh::lean_unsigned_to_nat(2);
                        v___x_195_ = lean_nat_dec_eq(v_x_189_, v___x_194_);
                        if v___x_195_ == 0 {
                            v___x_196_ = leanh::lean_unsigned_to_nat(3);
                            v___x_197_ = lean_nat_dec_eq(v_x_189_, v___x_196_);
                            if v___x_197_ == 0 {
                                v___x_198_ = leanh::lean_unsigned_to_nat(4);
                                v___x_199_ = lean_nat_dec_eq(v_x_189_, v___x_198_);
                                if v___x_199_ == 0 {
                                    v___x_200_ = leanh::lean_unsigned_to_nat(5);
                                    v___x_201_ = lean_nat_dec_eq(v_x_189_, v___x_200_);
                                    if v___x_201_ == 0 {
                                        v___x_202_ = leanh::lean_unsigned_to_nat(6);
                                        v___x_203_ = lean_nat_dec_eq(v_x_189_, v___x_202_);
                                        if v___x_203_ == 0 {
                                            v___x_204_ = leanh::lean_unsigned_to_nat(7);
                                            v___x_205_ = lean_nat_dec_eq(v_x_189_, v___x_204_);
                                            if v___x_205_ == 0 {
                                                v___x_206_ = leanh::lean_unsigned_to_nat(8);
                                                v___x_207_ = lean_nat_dec_eq(v_x_189_, v___x_206_);
                                                if v___x_207_ == 0 {
                                                    v___x_208_ =
                                                        leanh::lean_unsigned_to_nat(9);
                                                    v___x_209_ =
                                                        lean_nat_dec_eq(v_x_189_, v___x_208_);
                                                    if v___x_209_ == 0 {
                                                        v___x_210_ =
                                                            leanh::lean_unsigned_to_nat(10);
                                                        v___x_228_ =
                                                            lean_nat_dec_eq(v_x_189_, v___x_210_);
                                                        if v___x_228_ == 0 {
                                                            v___x_229_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    100,
                                                                );
                                                            v___x_230_ =
                                                                lean_nat_mod(v_x_189_, v___x_229_);
                                                            v___x_231_ = lean_nat_dec_lt(
                                                                v___x_210_, v___x_230_,
                                                            );
                                                            if v___x_231_ == 0 {
                                                                leanh::lean_dec(v___x_230_);
                                                                v___y_212_ = v___x_231_;
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_232_ = leanh::lean_unsigned_to_nat(20);
                                                                v___x_233_ = lean_nat_dec_lt(
                                                                    v___x_230_, v___x_232_,
                                                                );
                                                                leanh::lean_dec(v___x_230_);
                                                                v___y_212_ = v___x_233_;
                                                                state = 1;
                                                                continue;
                                                            }
                                                        } else {
                                                            leanh::lean_dec(v_x_189_);
                                                            v___x_234_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3;
                                                            return v___x_234_;
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_x_189_);
                                                        v___x_235_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4;
                                                        return v___x_235_;
                                                    }
                                                } else {
                                                    leanh::lean_dec(v_x_189_);
                                                    v___x_236_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5;
                                                    return v___x_236_;
                                                }
                                            } else {
                                                leanh::lean_dec(v_x_189_);
                                                v___x_237_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6;
                                                return v___x_237_;
                                            }
                                        } else {
                                            leanh::lean_dec(v_x_189_);
                                            v___x_238_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7;
                                            return v___x_238_;
                                        }
                                    } else {
                                        leanh::lean_dec(v_x_189_);
                                        v___x_239_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8;
                                        return v___x_239_;
                                    }
                                } else {
                                    leanh::lean_dec(v_x_189_);
                                    v___x_240_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9;
                                    return v___x_240_;
                                }
                            } else {
                                leanh::lean_dec(v_x_189_);
                                v___x_241_ =
                                    l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10;
                                return v___x_241_;
                            }
                        } else {
                            leanh::lean_dec(v_x_189_);
                            v___x_242_ =
                                l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11;
                            return v___x_242_;
                        }
                    } else {
                        leanh::lean_dec(v_x_189_);
                        v___x_243_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12;
                        return v___x_243_;
                    }
                } else {
                    leanh::lean_dec(v_x_189_);
                    v___x_244_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13;
                    return v___x_244_;
                }
            }
            1 => {
                if v___y_212_ == 0 {
                    v___x_213_ = lean_nat_mod(v_x_189_, v___x_210_);
                    v___x_214_ = lean_nat_dec_eq(v___x_213_, v___x_194_);
                    if v___x_214_ == 0 {
                        v___x_215_ = lean_nat_dec_eq(v___x_213_, v___x_196_);
                        leanh::lean_dec(v___x_213_);
                        if v___x_215_ == 0 {
                            v___x_216_ = l_Nat_reprFast(v_x_189_);
                            v___x_217_ =
                                l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0;
                            v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
                            return v___x_218_;
                        } else {
                            v___x_219_ = l_Nat_reprFast(v_x_189_);
                            v___x_220_ =
                                l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1;
                            v___x_221_ = lean_string_append(v___x_219_, v___x_220_);
                            return v___x_221_;
                        }
                    } else {
                        leanh::lean_dec(v___x_213_);
                        v___x_222_ = l_Nat_reprFast(v_x_189_);
                        v___x_223_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2;
                        v___x_224_ = lean_string_append(v___x_222_, v___x_223_);
                        return v___x_224_;
                    }
                } else {
                    v___x_225_ = l_Nat_reprFast(v_x_189_);
                    v___x_226_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0;
                    v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
                    return v___x_227_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_257_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__0;
    v___x_258_ = l_Lean_MessageData_ofFormat(v___x_257_);
    return v___x_258_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_261_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__2;
    v___x_262_ = l_Lean_MessageData_ofFormat(v___x_261_);
    return v___x_262_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_265_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__4;
    v___x_266_ = l_Lean_MessageData_ofFormat(v___x_265_);
    return v___x_266_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_269_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__6;
    v___x_270_ = l_Lean_MessageData_ofFormat(v___x_269_);
    return v___x_270_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_271_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7);
    v___x_272_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5);
    v___x_273_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3);
    v___x_274_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1);
    v___x_275_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_275_, 0, v___x_274_);
    leanh::lean_ctor_set(v___x_275_, 1, v___x_273_);
    leanh::lean_ctor_set(v___x_275_, 2, v___x_272_);
    leanh::lean_ctor_set(v___x_275_, 3, v___x_271_);
    return v___x_275_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData()
-> *mut leanh::LeanObject {
    let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_276_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8);
    return v___x_276_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__List_toOxford___redArg(
    mut v_inst_277_: *mut leanh::LeanObject,
    mut v_inst_278_: *mut leanh::LeanObject,
    mut v_x_279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_279_) == 0 {
        let mut v_emp_280_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_277_);
        v_emp_280_ = leanh::lean_ctor_get(v_inst_278_, 0);
        leanh::lean_inc(v_emp_280_);
        leanh::lean_dec_ref(v_inst_278_);
        return v_emp_280_;
    } else {
        let mut v_tail_281_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_281_ = leanh::lean_ctor_get(v_x_279_, 1);
        if leanh::lean_obj_tag(v_tail_281_) == 0 {
            let mut v_head_282_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_inst_278_);
            leanh::lean_dec(v_inst_277_);
            v_head_282_ = leanh::lean_ctor_get(v_x_279_, 0);
            leanh::lean_inc(v_head_282_);
            leanh::lean_dec_ref_known(v_x_279_, 2);
            return v_head_282_;
        } else {
            let mut v_tail_283_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_tail_281_);
            v_tail_283_ = leanh::lean_ctor_get(v_tail_281_, 1);
            if leanh::lean_obj_tag(v_tail_283_) == 0 {
                let mut v_head_284_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_head_285_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_and_286_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_head_284_ = leanh::lean_ctor_get(v_x_279_, 0);
                leanh::lean_inc(v_head_284_);
                leanh::lean_dec_ref_known(v_x_279_, 2);
                v_head_285_ = leanh::lean_ctor_get(v_tail_281_, 0);
                leanh::lean_inc(v_head_285_);
                leanh::lean_dec_ref_known(v_tail_281_, 2);
                v_and_286_ = leanh::lean_ctor_get(v_inst_278_, 1);
                leanh::lean_inc(v_and_286_);
                leanh::lean_dec_ref(v_inst_278_);
                leanh::lean_inc(v_inst_277_);
                v___x_287_ = leanh::lean_apply_2(v_inst_277_, v_head_284_, v_and_286_);
                v___x_288_ = leanh::lean_apply_2(v_inst_277_, v___x_287_, v_head_285_);
                return v___x_288_;
            } else {
                let mut v_tail_289_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_tail_289_ = leanh::lean_ctor_get(v_tail_283_, 1);
                if leanh::lean_obj_tag(v_tail_289_) == 0 {
                    let mut v_head_290_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_head_291_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_head_292_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_comma_293_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_commaAnd_294_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_inc_ref(v_tail_283_);
                    v_head_290_ = leanh::lean_ctor_get(v_x_279_, 0);
                    leanh::lean_inc(v_head_290_);
                    leanh::lean_dec_ref_known(v_x_279_, 2);
                    v_head_291_ = leanh::lean_ctor_get(v_tail_281_, 0);
                    leanh::lean_inc(v_head_291_);
                    leanh::lean_dec_ref_known(v_tail_281_, 2);
                    v_head_292_ = leanh::lean_ctor_get(v_tail_283_, 0);
                    leanh::lean_inc(v_head_292_);
                    leanh::lean_dec_ref_known(v_tail_283_, 2);
                    v_comma_293_ = leanh::lean_ctor_get(v_inst_278_, 2);
                    leanh::lean_inc(v_comma_293_);
                    v_commaAnd_294_ = leanh::lean_ctor_get(v_inst_278_, 3);
                    leanh::lean_inc(v_commaAnd_294_);
                    leanh::lean_dec_ref(v_inst_278_);
                    leanh::lean_inc_n(v_inst_277_, 3);
                    v___x_295_ = leanh::lean_apply_2(v_inst_277_, v_head_290_, v_comma_293_);
                    v___x_296_ = leanh::lean_apply_2(v_inst_277_, v___x_295_, v_head_291_);
                    v___x_297_ =
                        leanh::lean_apply_2(v_inst_277_, v___x_296_, v_commaAnd_294_);
                    v___x_298_ = leanh::lean_apply_2(v_inst_277_, v___x_297_, v_head_292_);
                    return v___x_298_;
                } else {
                    let mut v_head_299_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_comma_300_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v_head_299_ = leanh::lean_ctor_get(v_x_279_, 0);
                    leanh::lean_inc(v_head_299_);
                    leanh::lean_dec_ref_known(v_x_279_, 2);
                    v_comma_300_ = leanh::lean_ctor_get(v_inst_278_, 2);
                    leanh::lean_inc_n(v_inst_277_, 2);
                    leanh::lean_inc(v_comma_300_);
                    v___x_301_ = leanh::lean_apply_2(v_inst_277_, v_head_299_, v_comma_300_);
                    v___x_302_ = l___private_Lean_Elab_ErrorUtils_0__List_toOxford___redArg(
                        v_inst_277_,
                        v_inst_278_,
                        v_tail_281_,
                    );
                    v___x_303_ = leanh::lean_apply_2(v_inst_277_, v___x_301_, v___x_302_);
                    return v___x_303_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__List_toOxford(
    mut v_00_u03b1_304_: *mut leanh::LeanObject,
    mut v_inst_305_: *mut leanh::LeanObject,
    mut v_inst_306_: *mut leanh::LeanObject,
    mut v_x_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = l___private_Lean_Elab_ErrorUtils_0__List_toOxford___redArg(
        v_inst_305_,
        v_inst_306_,
        v_x_307_,
    );
    return v___x_308_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0(
    mut v_x_310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_311_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0___closed__0;
    v___x_312_ = lean_string_append(v_x_310_, v___x_311_);
    return v___x_312_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_318_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0___closed__0;
    v___x_319_ = l_Lean_stringToMessageData(v___x_318_);
    return v___x_319_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0(
    mut v_x_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0);
    v___x_322_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_322_, 0, v_x_320_);
    leanh::lean_ctor_set(v___x_322_, 1, v___x_321_);
    return v___x_322_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1()
-> *mut leanh::LeanObject {
    let mut v___f_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_324_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__0;
    v___x_325_ = l_Lean_MessageData_nil;
    v___x_326_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_326_, 0, v___x_325_);
    leanh::lean_ctor_set(v___x_326_, 1, v___f_324_);
    return v___x_326_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData()
-> *mut leanh::LeanObject {
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1);
    return v___x_327_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural___redArg(
    mut v_count_328_: *mut leanh::LeanObject,
    mut v_singular_329_: *mut leanh::LeanObject,
    mut v_plural_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: u8 = 0;
    v___x_331_ = leanh::lean_unsigned_to_nat(1);
    v___x_332_ = lean_nat_dec_eq(v_count_328_, v___x_331_);
    if v___x_332_ == 0 {
        leanh::lean_inc(v_plural_330_);
        return v_plural_330_;
    } else {
        leanh::lean_inc(v_singular_329_);
        return v_singular_329_;
    }
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural___redArg___boxed(
    mut v_count_333_: *mut leanh::LeanObject,
    mut v_singular_334_: *mut leanh::LeanObject,
    mut v_plural_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_336_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___redArg(
        v_count_333_,
        v_singular_334_,
        v_plural_335_,
    );
    leanh::lean_dec(v_plural_335_);
    leanh::lean_dec(v_singular_334_);
    leanh::lean_dec(v_count_333_);
    return v_res_336_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural(
    mut v_00_u03b1_337_: *mut leanh::LeanObject,
    mut v_inst_338_: *mut leanh::LeanObject,
    mut v_count_339_: *mut leanh::LeanObject,
    mut v_singular_340_: *mut leanh::LeanObject,
    mut v_plural_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___redArg(
        v_count_339_,
        v_singular_340_,
        v_plural_341_,
    );
    return v___x_342_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural___boxed(
    mut v_00_u03b1_343_: *mut leanh::LeanObject,
    mut v_inst_344_: *mut leanh::LeanObject,
    mut v_count_345_: *mut leanh::LeanObject,
    mut v_singular_346_: *mut leanh::LeanObject,
    mut v_plural_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural(
        v_00_u03b1_343_,
        v_inst_344_,
        v_count_345_,
        v_singular_346_,
        v_plural_347_,
    );
    leanh::lean_dec(v_plural_347_);
    leanh::lean_dec(v_singular_346_);
    leanh::lean_dec(v_count_345_);
    leanh::lean_dec_ref(v_inst_344_);
    return v_res_348_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ErrorUtils(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Message(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData =
        _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData();
    leanh::lean_mark_persistent(
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData,
    );
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData =
        _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData();
    leanh::lean_mark_persistent(
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ErrorUtils(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ErrorUtils(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Message(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ErrorUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ErrorUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_ErrorUtils(builtin);
}